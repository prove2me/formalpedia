-- Prove2me | Theorems.Thm_SparseSDP_TwoSided_Supplement_theorem_6_2
-- name    : SparseSDP.TwoSided.Supplement.theorem_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:34:27.767266+00:00
-- url     : https://prove2.me/theorems/c1afd766-e657-4c64-b23e-9f64ae26df2c
-- title:
--   Theorem 6.2, pp. 42–43 — the classical Gibbs–MMWU solver returns a valid primal or dual certificate w.p. $1-\delta$, support $\tilde O(\gamma^2)$, time $\tilde O(ns\gamma^{13/2}+ms\gamma^4)$
-- statement:
--   Consider an SDP of the form (1), (2) under the sparse-access model of Definition 2.1, with $C,A_j$ Hermitian of operator norm at most one and row sparsity $s$. Assume strong duality, supplied primal and dual radii $R,r\ge1$, and the normalization $A_1=I$, $b_1=R$. Let $\gamma=Rr/\varepsilon\ge1$. For every target $g\in[-R,R]$ and failure probability $\delta\in(0,1)$, the solver (Algorithm 6, the primal phase, and the certificate selection of the proof) has the following guarantees.
--
--   1. **Primal certificate.** If $\mathrm{OPT}\ge g+\varepsilon$, it returns coefficients $y'=(y_0',\dots,y_m')\in\mathbb R^{m+1}_{\ge0}$ and $z\in[0,R]$ defining
--   $$
--   X=z\cdot\frac{\exp\big(y_0'C-\sum_{j=1}^my_j'A_j\big)}{\operatorname{Tr}\exp\big(y_0'C-\sum_{j=1}^my_j'A_j\big)},
--   $$
--   which satisfies $\langle C,X\rangle\ge g-\varepsilon$ and $\langle A_j,X\rangle\le b_j+\varepsilon/r$ for every $j\in[m]$.
--   2. **Dual certificate.** If $\mathrm{OPT}\le g-\varepsilon$, it returns $y\in\mathbb R^m_{\ge0}$ with
--   $$
--   \sum_{j=1}^my_jA_j-C\succeq-\varepsilon I,\qquad b^\top y\le g+\varepsilon .
--   $$
--
--   Either output is permitted when $\mathrm{OPT}\in[g-\varepsilon,g+\varepsilon]$. With probability at least $1-\delta$ the returned certificate is valid. The coefficient representation has support $\tilde O(\gamma^2)$ and the running time is $\tilde O(ns\gamma^{13/2}+ms\gamma^4)$.
--
--   Here $\tilde O(f)$ means at most $C_cfL^\kappa$ with universal $C_c,\kappa$ and $L=\log(2+n+m+\gamma+1/\delta)$. For constant $\gamma$ and $s$ the time is $\tilde O(n+m)$: the solver's dependence on $n$ and $m$ is additive, because each filtered random vector is reused for all $m$ constraints.
--
--   **Formalization Note** On one event of probability at least $1-\delta$ the Lean statement asserts: the output is primal if $\mathrm{OPT}\ge g+\varepsilon$, dual if $\mathrm{OPT}\le g-\varepsilon$, and in all cases the returned certificate satisfies the inequalities of its kind (so also in the middle band). $A_1$, $b_1$ are Lean's `I.A ⟨0,_⟩`, `I.b ⟨0,_⟩`.
--
--   Differences from the source:
--   - reading: there is an exact-arithmetic sparse-oracle algorithm → the concrete charged program `solve62` (Algorithm 6, the primal phase of p. 42 and the certificate selection of p. 43), with the universal constants of Algorithm 5 existentially quantified before the instance; reason: base reading R1; the proof analyses exactly this procedure
--   - reading: the θ-oracle's geometric step of [vAGGdW20, Lemma 16] → one exact primitive returning a point of $\hat P$ with at most two nonzeros among $1,\dots,m$, or none exactly when no such point exists, charged $16(m+1)$; reason: the routine is not in the paper; p. 43 gives its specification and its $O(m)$ cost, as for the base mission's tridiagonal primitives (R3)
--   - reading: the constant $c>0$ of [vAGGdW20, Lemma 16] and the per-call failure budgets → $c=1/2$; budgets $\delta/(2T)$ per Algorithm 6 call and $\delta/(2T_P)$ per primal-phase call; reason: the proof makes $c\le1/2$ explicit (p. 43) and allows any split summing to at most $\delta$
--   - reading: running time in the idealized real-arithmetic model → the final counter of the published `Prog` model, complex scalar operations charged as a fixed number of real ones; reason: base readings R2–R3
--   - reading: $\tilde O(f)$ → $C_cfL^\kappa$ with universal $C_c,\kappa$ and the published $L=\log(2+n+m+\gamma+1/\delta)$; reason: base reading R4; all logarithms of the proof are polylogarithmic in $L$ since $r\ge1$
--   - generalization: running time and support → bounds on every tape; reason: the round counts $T$, $T_P$ are deterministic; stronger than a bound on the success event
--   - encoding: with probability at least $1-\delta$, the returned certificate is valid → the failure set (of the conjunction of the two case implications and validity) has outer measure at most $\delta$ under the tape law; reason: no measurability needs assuming; for a measurable event it is the same statement
--   - encoding: $\gamma:=Rr/\varepsilon\ge1$ → $0<\varepsilon$ and $1\le R r/\varepsilon$; reason: $\gamma$ is undefined at $\varepsilon=0$; a nondegeneracy condition excluding only that case
--   - encoding: the normalization $A_1=I$, $b_1=R$ → $\exists\,h:0<m$, `I.A ⟨0,h⟩ = 1 ∧ I.b ⟨0,h⟩ = R`, and `[NeZero n]`; reason: Lean indexes constraints from $0$; $m\ge1$ and $n\ge1$ are already implied by `Normalized`
--   - generalization: the $k$-th nonzero of a row (Definition 2.1) → any fixed enumeration of the row's nonzeros without repetition; reason: base reading R9: column order is one instance
-- source:
--   Brandão, Dalzell, Gilyén, Vasconcelos, Solving Sparse SDPs in Sublinear Time, arXiv:2609.40302, Theorem 6.2, pp. 42–43, Eqs. (221)–(222); Algorithm 6, p. 41; §6.2, pp. 41–42; proof, pp. 43–44

import Mathlib
import Definitions.Def_SparseSDP_TwoSided_alg7
import Definitions.Def_SparseSDP_TwoSided_Supplement_solve62

open Matrix MeasureTheory

namespace SparseSDP.TwoSided.Supplement

open SparseSDP.TwoSided

/-- **Theorem 6.2** (Direct Classical Gibbs–MMWU Solver), pp. 42–43.

Brandão, Dalzell, Gilyén, Vasconcelos, *Solving Sparse SDPs in Sublinear Time*, arXiv:2609.40302,
Theorem 6.2, pp. 42–43; Algorithm 6, p. 41; §6.2, pp. 41–42; proof, pp. 43–44.

`P`, `Cc`, `κ` are universal, chosen before the instance. For every normalized Hermitian instance
(operator norm at most one, row sparsity `s`) with strong duality within radii `R, r ≥ 1`, with
`A₁ = I` and `b₁ = R`, every `ε > 0` with `γ = Rr/ε ≥ 1`, every target `g ∈ [−R, R]` and every
`δ ∈ (0, 1)`: on every tape the solver costs at most `Cc (nsγ^{13/2} + msγ⁴) L^κ` and its output has
at most `Cc γ² L^κ` nonzero coefficients, `L = log(2 + n + m + γ + 1/δ)`; and except with
probability `δ` (1) if `OPT ≥ g + ε` the output is primal, (2) if `OPT ≤ g − ε` it is dual, and
the returned certificate is valid (`Cert62.Valid`: Eq. (221) and its two inequalities, or Eq. (222)),
also when `OPT ∈ (g − ε, g + ε)`, where either output is permitted.

**Formalization Note.** "There is an algorithm" is read as a statement about the concrete program
`solve62` (base reading R1), which reads the instance only through `qCol`, `qEntry`, `qB`. The
θ-oracle's geometric step is one exact primitive charged `16(m + 1)` (`thetaOracle`). The paper's
`A₁`, `b₁` are Lean's `I.A ⟨0, _⟩`, `I.b ⟨0, _⟩`. The failure set is bounded in outer measure. -/
theorem theorem_6_2 :
    ∃ (P : Consts5) (Cc : ℝ) (κ : ℕ), 0 < Cc ∧
    ∀ (n m s : ℕ) [NeZero n] (I : Instance ℂ n m) (orc : SparseOracle I) (R r ε g δ OPT : ℝ),
      I.Normalized s → 1 ≤ R → 1 ≤ r → StrongDuality I R r OPT →
      (∃ h : 0 < m, I.A ⟨0, h⟩ = 1 ∧ I.b ⟨0, h⟩ = R) →
      0 < ε → 1 ≤ R * r / ε → -R ≤ g → g ≤ R → 0 < δ → δ < 1 →
      (∀ tape : Tape,
        (runCost (solve62 P orc R r ε g δ) tape : ℝ) ≤
          Cc * ((n : ℝ) * s * (R * r / ε) ^ (13 / 2 : ℝ) + (m : ℝ) * s * (R * r / ε) ^ 4) *
            polyL n m (R * r / ε) δ ^ κ ∧
        ((runVal (solve62 P orc R r ε g δ) tape).support : ℝ) ≤
          Cc * (R * r / ε) ^ 2 * polyL n m (R * r / ε) δ ^ κ) ∧
      tapeLaw {tape | ¬ ((g + ε ≤ OPT → (runVal (solve62 P orc R r ε g δ) tape).IsPrimal) ∧
          (OPT ≤ g - ε → ¬ (runVal (solve62 P orc R r ε g δ) tape).IsPrimal) ∧
          (runVal (solve62 P orc R r ε g δ) tape).Valid I R r ε g)} ≤ ENNReal.ofReal δ := by sorry

end SparseSDP.TwoSided.Supplement
