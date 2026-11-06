-- Prove2me | Theorems.Thm_SparseSDP_TwoSided_end_to_end_solver
-- name    : SparseSDP.TwoSided.end_to_end_solver
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T21:00:59.000419+00:00
-- url     : https://prove2.me/theorems/ede2092b-1ade-480b-a357-87b89b360c28
-- title:
--   Corollary 7.11, p. 63 — a randomized sparse-oracle SDP solver in time $\tilde O(ns\min\{\gamma^2,m,n/s\}\gamma^{5/2}+(n+ms)\gamma^2)$
-- statement:
--   Consider an SDP of the form (1), (2) under sparse access, with $C,A_j$ Hermitian, $s$-row-sparse, of operator norm at most one, with strong duality and supplied radii $R,r\ge1$. For every $\varepsilon,\delta\in(0,1)$, with $\gamma=Rr/\varepsilon$, the randomized exact-arithmetic sparse-oracle algorithm `sdpSolve` returns, with probability at least $1-\delta$, a matrix $\hat X\succeq0$ with $\operatorname{Tr}\hat X\le R$ and
--   $$
--   \langle C,\hat X\rangle\ge\mathrm{OPT}-\varepsilon,\qquad\langle A_j,\hat X\rangle\le b_j+\frac\varepsilon r\quad\forall j\in[m].
--   $$
--   The output is represented by $\tilde O(\gamma^2)$ rank-one factors, and the running time is
--   $$
--   \tilde O\big(ns\min\{\gamma^2,m,n/s\}\gamma^{5/2}+(n+ms)\gamma^2\big).
--   $$
--
--   Here $\tilde O(f)$ means at most $C_cfL^\kappa$ with universal $C_c,\kappa$ and $L=\log(2+n+m+\gamma+1/\delta)$. For fixed $\gamma$ and $s$ the time is $\tilde O(n+m)$, sublinear in the $\Theta(mns)$ size of the input.
--
--   Differences from the source:
--   - reading: there is a randomized exact-arithmetic sparse-oracle algorithm → the concrete instrumented program `sdpSolve` in the `Work` monad, with running time its final counter; reason: R1: an existential over a shallow monad would be empty; the statement about one explicit program is stronger
--   - reading: the idealized real-arithmetic model of §2.2 → unit cost for $+,-,\times,\div,\sqrt{\cdot},\exp,\log$, comparison, $\lceil\cdot\rceil$, array access, loop dispatch, one draw, one oracle call; reason: R2: the paper's accounting needs $\exp$ and $\sqrt{\cdot}$ at unit cost (p. 62)
--   - reading: the exponential of the tridiagonal compression, and the Ritz value of Lemma 2.5 → two exact primitives on $T_\ell$, charged $\ell^2$; reason: R3: neither is finite arithmetic; the paper charges $O(q^2)$ for the first (p. 27) and nothing for the second
--   - reading: $\tilde O(f)$ → $C_cfL^\kappa$ with universal $C_c,\kappa$ and $L=\log(2+n+m+\gamma+1/\delta)$; reason: R4: all logarithms of the proof are polylogarithms of $L$, since $r\ge1$ gives $R/\varepsilon\le\gamma$
--   - generalization: running time, proved with $T$, $K$, $k_t$ deterministic → the bound on every tape, not only on the success event; reason: R5: stronger than an expected or high-probability bound, and the proof gives it
--   - encoding: randomized algorithm → one tape of i.i.d. pairs $(g,v)$, $g\sim N(0,1)$, $v$ uniform on $[0,1]$, under `Measure.infinitePi`; reason: R6: a draw reads one slot; $\mathrm{Unif}(S^{d-1})$ is $d$ normalized Gaussians
--   - encoding: with probability at least $1-p$ → the failure set has outer measure at most $p$ under `tapeLaw`; reason: no measurability of the event needs assuming; for a measurable event it is the same statement
--   - reading: the $\Theta$ and sufficiently-large constants of Algorithm 7 and Corollary 7.11 → one `Consts`, existentially quantified before the instance; reason: R7
--   - encoding: OPT with strong duality → a real number with `IsGreatest` and `IsLeast`, attained within the radii; reason: R8: no `sSup`, so no junk value
--   - generalization: the $k$-th nonzero of a row (Definition 2.1) → any fixed enumeration of the row's nonzeros without repetition; reason: R9: column order is one instance
--   - reading: the primal output is represented implicitly by $\tilde O(\gamma^2)$ rank-one factors → $\hat X=\sum_{v\in L}vv^\dagger$ for the returned list $L$ of vectors of $\mathbb C^n$; reason: R10: the weight $R/T$ is absorbed in $v$; $\Psi$ maps a real factor $(x,y)$ to $x+iy$ (Eq. (383))
--   - reading: the dual output of the game solver is represented by the constraint-sampling counts (p. 47) → the field `rep.cnt` of `Alg7Out`; Corollary 7.11 itself claims no dual output; reason: R11
--   - encoding: $j\in[m]$ ranging over the constraints → `Normalized` includes $1\le m$; reason: a nondegeneracy condition that only excludes an undefined case: the page's $\min_{j\in[m]}$ and the $\log(2m)$, $\log(16mn/\delta)$ of Algorithm 7 presuppose $m\ge1$
-- source:
--   Brandão, Dalzell, Gilyén, Vasconcelos, Solving Sparse SDPs in Sublinear Time, arXiv:2609.40302, Corollary 7.11, p. 63, Eqs. (359)–(361)

import Mathlib
import Definitions.Def_SparseSDP_TwoSided_sdpSolve

open Matrix MeasureTheory

namespace SparseSDP.TwoSided

/-- **Corollary 7.11** (End-to-End Two-Sided Stochastic SDP Solver), p. 63.

Brandão, Dalzell, Gilyén, Vasconcelos, *Solving Sparse SDPs in Sublinear Time*, arXiv:2609.40302,
Corollary 7.11, p. 63.

`P`, `Cc`, `κ` are universal, chosen before the instance. For every normalized Hermitian instance
with strong duality and radii `R, r ≥ 1`, and all `ε, δ ∈ (0, 1)`, with `γ = Rr/ε` and
`L = log(2 + n + m + γ + 1/δ)`: on every tape the concrete program `sdpSolve` costs at most
`Cc (ns min{γ², m, n/s} γ^{5/2} + (n + ms)γ²) L^κ` and returns at most `Cc γ² L^κ` rank-one factors;
and except with probability `δ` the sum of the factors solves the SDP to additive error `ε`.

**Formalization Note.** Readings R1–R11 of the mission: `sdpSolve` reads the instance only
through `qCol`, `qEntry`, `qB`; the failure set is bounded in outer measure, so no measurability of
the event is assumed. -/
theorem end_to_end_solver :
    ∃ (P : Consts) (Cc : ℝ) (κ : ℕ), 0 < Cc ∧
    ∀ (n m s : ℕ) (I : Instance ℂ n m) (orc : SparseOracle I) (R r ε δ OPT : ℝ),
      I.Normalized s → 1 ≤ R → 1 ≤ r → StrongDuality I R r OPT →
      0 < ε → ε < 1 → 0 < δ → δ < 1 →
      (∀ tape : Tape,
        (runCost (sdpSolve P s R r ε δ orc) tape : ℝ) ≤
          Cc * ((n : ℝ) * s * min ((R * r / ε) ^ 2) (min (m : ℝ) ((n : ℝ) / s)) *
                (R * r / ε) ^ (5 / 2 : ℝ) +
              ((n : ℝ) + m * s) * (R * r / ε) ^ 2) *
            polyL n m (R * r / ε) δ ^ κ ∧
        ((runVal (sdpSolve P s R r ε δ orc) tape).length : ℝ) ≤
          Cc * (R * r / ε) ^ 2 * polyL n m (R * r / ε) δ ^ κ) ∧
      tapeLaw {tape | ¬ IsApproxSolution I R r ε OPT
          (factorSum (runVal (sdpSolve P s R r ε δ orc) tape))} ≤ ENNReal.ofReal δ := by sorry

end SparseSDP.TwoSided
