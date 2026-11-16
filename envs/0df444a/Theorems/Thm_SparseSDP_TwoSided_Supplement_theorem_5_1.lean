-- Prove2me | Theorems.Thm_SparseSDP_TwoSided_Supplement_theorem_5_1
-- name    : SparseSDP.TwoSided.Supplement.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:33:40.678854+00:00
-- url     : https://prove2.me/theorems/3419fde4-3049-4707-a80c-be80f9ae4746
-- title:
--   Theorem 5.1, pp. 27–28 — Algorithm 5 estimates all $m$ Gibbs expectations to $\pm\alpha$ w.p. $1-\delta$ in $\tilde O\big(\tfrac{\omega^2}{\alpha^2}[n(hs_B+1)\min\{n,\sqrt{1+B_H}\}+ms_A]\big)$ time
-- statement:
--   Let $H=\sum_{\ell=1}^h y_\ell B_\ell$ with $y\in\mathbb R^h$ and $\|y\|_1\le B_H$, where each $B_\ell\in\mathbb C^{n\times n}$ is Hermitian, $s_B$-row-sparse and $\|B_\ell\|\le1$. Let $A_1,\dots,A_m\in\mathbb C^{n\times n}$ be Hermitian, $s_A$-row-sparse, with $\|A_j\|\le\omega$. All matrices are given by sparse oracle access, and $\Omega_H=e^{-H}/\operatorname{Tr}(e^{-H})$. For any accuracy $\alpha\in(0,\omega]$ and failure probability $\delta\in(0,1)$, Algorithm 5 outputs estimates $\hat\mu_1,\dots,\hat\mu_m$ with
--   $$
--   \mathbb P\Big[\max_{j\in[m]}\big|\hat\mu_j-\operatorname{Tr}(A_j\Omega_H)\big|\le\alpha\Big]\ge1-\delta,
--   $$
--   and its sparse-oracle running time is
--   $$
--   \tilde O\Big(\frac{\omega^2}{\alpha^2}\Big[n(hs_B+1)\min\big\{n,\sqrt{1+B_H}\big\}+ms_A\Big]\Big).
--   $$
--
--   Here $\tilde O(f)$ means at most $C_cfL^\kappa$ with universal $C_c,\kappa$ and $L=\log(2+n+m+\omega/\alpha+1/\delta)$; the universal constants of Algorithm 5 are chosen once, before the input.
--
--   The Hamiltonian-dependent filtering $e^{-H/2}u$ is computed once per random start and reused for every observable, so the dependence on $m$ is only the additive $ms_A$ readout term. This is the estimation primitive behind the classical Gibbs–MMWU solver of Theorem 6.2.
--
--   **Formalization Note** The row sparsities satisfy $1\le s_B,s_A\le n$ (the convention of Definition 2.1) and $n\ge1$.
--
--   Differences from the source:
--   - reading: there is a randomized exact-arithmetic algorithm → the concrete charged program `alg5` (Algorithm 5), with its universal constants $c_g,c_b,c_0,C_L$ existentially quantified before the input; reason: base reading R1: an existential over programs in the shallow `Work` monad would be empty; the proof analyses Algorithm 5
--   - reading: sparse-oracle running time in the idealized real-arithmetic model → the final counter of the published `Prog` model; a complex addition costs 2, a complex multiplication 6 real operations; the median of $g$ values costs $g^2+1$; reason: base readings R2–R3; a complex scalar operation is a fixed number of real ones
--   - reading: $\tilde O(f)$ → $C_cfL^\kappa$ with universal $C_c,\kappa$ and $L=\log(2+n+m+\omega/\alpha+1/\delta)$; reason: every logarithm of the proof ($g$, $L_H$, Eqs. (173)–(176), (203)) is polylogarithmic in $L$
--   - generalization: running time → the bound on every tape; reason: $N$ and $q_H$ are deterministic, so the proof's bound (202)–(206) holds for every realization; stronger than a bound on the success event
--   - encoding: with probability at least $1-\delta$ → the failure set has outer measure at most $\delta$ under the published tape law; reason: no measurability of the event needs assuming; for a measurable event it is the same statement
--   - reading: $\operatorname{median}_{a\in[g]}$ → the lower median, and $g,b$ at least one; reason: the page does not fix the median of an even number of values; $g\ge1$ only matters at $m=0$
--   - encoding: $n\times n$ matrices with $s$-row-sparsity, $1\le s\le n$ (Definition 2.1) → `[NeZero n]`, $1\le s_B\le n$, $1\le s_A\le n$; reason: the convention of Definition 2.1, stated once for all row-sparsity bounds
--   - generalization: the $k$-th nonzero of a row (Definition 2.1) → any fixed enumeration of the row's nonzeros without repetition; reason: base reading R9: column order is one instance
-- source:
--   Brandão, Dalzell, Gilyén, Vasconcelos, Solving Sparse SDPs in Sublinear Time, arXiv:2609.40302, Theorem 5.1, pp. 27–28, Eqs. (99)–(100); Algorithm 5, p. 36; proof §5.5, pp. 35–39

import Mathlib
import Definitions.Def_SparseSDP_TwoSided_alg7
import Definitions.Def_SparseSDP_TwoSided_Supplement_gibbs
import Definitions.Def_SparseSDP_TwoSided_Supplement_alg5

open Matrix MeasureTheory
open scoped Matrix.Norms.L2Operator

namespace SparseSDP.TwoSided.Supplement

open SparseSDP.TwoSided

/-- **Theorem 5.1** (Efficient Simultaneous Gibbs Expectation Estimation), pp. 27–28.

Brandão, Dalzell, Gilyén, Vasconcelos, *Solving Sparse SDPs in Sublinear Time*, arXiv:2609.40302,
Theorem 5.1, pp. 27–28; Algorithm 5, p. 36; proof §5.5, pp. 35–39.

The constants `P` of Algorithm 5 and `Cc`, `κ` of `Õ` are universal, chosen before the input. For
`H = ∑_{ℓ=1}^h y_ℓ B_ℓ` with `‖y‖₁ ≤ B_H`, Hermitian `s_B`-row-sparse `B_ℓ` with `‖B_ℓ‖ ≤ 1`,
Hermitian `s_A`-row-sparse observables `Aⱼ` with `‖Aⱼ‖ ≤ ω`, `α ∈ (0, ω]` and `δ ∈ (0, 1)`: on every
tape Algorithm 5 costs at most `Cc (ω²/α²)[n(hs_B + 1) min{n, √(1 + B_H)} + ms_A] L^κ` with
`L = log(2 + n + m + ω/α + 1/δ)`, and except with probability `δ` all estimates satisfy
`|μ̂ⱼ − Tr(AⱼΩ_H)| ≤ α` simultaneously.

**Formalization Note.** "There is an algorithm" is read as a statement about the concrete program
`alg5` (base reading R1); it reads the matrices only through the sparse oracles `orcB`, `orcA`.
`1 ≤ s_B, s_A ≤ n` is the convention of Definition 2.1; `[NeZero n]` excludes the empty matrix
size. The failure set is bounded in `tapeLaw` outer measure. `‖·‖` is the operator norm. -/
theorem theorem_5_1 :
    ∃ (P : Consts5) (Cc : ℝ) (κ : ℕ), 0 < Cc ∧
    ∀ (n h m sB sA : ℕ) [NeZero n] (B : Fin h → Matrix (Fin n) (Fin n) ℂ)
      (A : Fin m → Matrix (Fin n) (Fin n) ℂ) (orcB : FamOracle B) (orcA : FamOracle A)
      (y : Fin h → ℝ) (BH ω α δ : ℝ),
      (∀ ℓ, (B ℓ).IsHermitian) → (∀ ℓ, RowSparse (B ℓ) sB) → (∀ ℓ, ‖B ℓ‖ ≤ 1) →
      (∀ j, (A j).IsHermitian) → (∀ j, RowSparse (A j) sA) → (∀ j, ‖A j‖ ≤ ω) →
      1 ≤ sB → sB ≤ n → 1 ≤ sA → sA ≤ n →
      ∑ ℓ, |y ℓ| ≤ BH → 0 < α → α ≤ ω → 0 < δ → δ < 1 →
      (∀ tape : Tape,
        (runCost (alg5 P (famAccess orcB) (hamList y) BH m (famAccess orcA) ω α δ) tape : ℝ) ≤
          Cc * ((ω / α) ^ 2 * ((n : ℝ) * ((h : ℝ) * sB + 1) * min (n : ℝ) √(1 + BH) +
              (m : ℝ) * sA)) * polyL n m (ω / α) δ ^ κ) ∧
      tapeLaw {tape | ¬ ∀ j, |runVal (alg5 P (famAccess orcB) (hamList y) BH m (famAccess orcA)
          ω α δ) tape j - gibbsExpect (A j) (adj B y)| ≤ α} ≤ ENNReal.ofReal δ := by sorry

end SparseSDP.TwoSided.Supplement
