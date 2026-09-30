-- Prove2me | Theorems.Thm_StochQuasiNewton_SQN_curvature_pair_bounds
-- name    : StochQuasiNewton.SQN.curvature_pair_bounds
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T19:52:09.686095+00:00
-- url     : https://prove2.me/theorems/edb66ac4-913f-4f59-a2e9-83438a1335ba
-- title:
--   Eqs. (3.8)–(3.10) — curvature bounds for the correction pairs
-- statement:
--   Let $f_1,\dots,f_N$ be $C^2$ functions on $\mathbb R^n$, let $0<\lambda$, $0<\Lambda$, and suppose that every subsampled Hessian with $b_H$ samples satisfies $\lambda I\prec\nabla^2F_{\mathcal S_H}(w)\prec\Lambda I$ for all $w$ (Assumption 1(2), Eq. (3.3)). Let $\mathcal S_H$ be a sample with $|\mathcal S_H|=b_H$, let $\bar w\in\mathbb R^n$, let $s\neq0$, and let $y=\nabla^2F_{\mathcal S_H}(\bar w)\,s$ as in (3.8). Then
--   $$\lambda\|s\|^2\le y^Ts\le\Lambda\|s\|^2\qquad\text{and}\qquad\lambda\le\frac{\|y\|^2}{y^Ts}\le\Lambda .$$
--
--   These are the curvature bounds (3.9) and (3.10) for the correction pairs of the SQN method; they bound the scaling $B_t^{(0)}$ and each rank-two term of the L-BFGS update in the proof of Lemma 3.1.
--
--   **Formalization Note** The statement is for an arbitrary nonzero $s$ and arbitrary point $\bar w$; in the paper $s=s_j=\bar w_j-\bar w_{j-1}$ and $\bar w=\bar w_j$.
-- source:
--   Byrd, Hansen, Nocedal, Singer, A Stochastic Quasi-Newton Method for Large-Scale Optimization, SIAM J. Optim. 26(2) (2016), p. 1015, Eqs. (3.8)–(3.10)

import Mathlib
import Definitions.Def_StochQuasiNewton_SQN_FiniteSum

open scoped RealInnerProductSpace

namespace StochQuasiNewton.SQN

/-- Eqs. (3.8)–(3.10): if every subsampled Hessian with `b_H` samples satisfies
`λ I ≺ ∇²F_{S_H}(w) ≺ Λ I` (3.3) with `0 < λ` and `0 < Λ`, then a correction pair `y = ∇²F_{S_H}(w̄) s` with `s ≠ 0`
satisfies `λ ‖s‖² ≤ yᵀs ≤ Λ ‖s‖²` (3.9) and `λ ≤ ‖y‖² / (yᵀs) ≤ Λ` (3.10). -/
theorem curvature_pair_bounds {n N : ℕ} (f : Fin N → EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ∀ i, ContDiff ℝ 2 (f i)) (lam Lam : ℝ) (hlam : 0 < lam) (hLam : 0 < Lam) (bH : ℕ)
    (hHess : ∀ SH : Finset (Fin N), SH.card = bH → ∀ w : EuclideanSpace ℝ (Fin n),
      StrictLoewnerBounds lam Lam (subsampledHessian f SH w))
    (SH : Finset (Fin N)) (hSH : SH.card = bH) (wbar s y : EuclideanSpace ℝ (Fin n))
    (hs : s ≠ 0) (hy : y = subsampledHessian f SH wbar s) :
    (lam * ‖s‖ ^ 2 ≤ ⟪y, s⟫ ∧ ⟪y, s⟫ ≤ Lam * ‖s‖ ^ 2) ∧
      (lam ≤ ‖y‖ ^ 2 / ⟪y, s⟫ ∧ ‖y‖ ^ 2 / ⟪y, s⟫ ≤ Lam) := by sorry

end StochQuasiNewton.SQN
