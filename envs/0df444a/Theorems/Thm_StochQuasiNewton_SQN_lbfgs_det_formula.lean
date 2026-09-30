-- Prove2me | Theorems.Thm_StochQuasiNewton_SQN_lbfgs_det_formula
-- name    : StochQuasiNewton.SQN.lbfgs_det_formula
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T19:53:10.503496+00:00
-- url     : https://prove2.me/theorems/ad733341-7bdd-43b6-b4f0-1d6f385d3806
-- title:
--   Eq. (3.12) — Powell's determinant formula for the L-BFGS cycle
-- statement:
--   Under the hypotheses of Eq. (3.11) (pairs in memory with $s_j\neq0$ and $y_j$ a subsampled-Hessian product, $M,t\ge1$, $\tilde m=\min\{t,M\}$), put $j_i=t-\tilde m+i$. Then the direct L-BFGS matrices (3.7) satisfy
--   $$\det\big(B_t^{(\tilde m)}\big)=\det\big(B_t^{(0)}\big)\prod_{i=1}^{\tilde m}\frac{y_{j_i}^Ts_{j_i}}{s_{j_i}^TB_t^{(i-1)}s_{j_i}} .$$
--
--   Combined with (3.9) and (3.11), this formula bounds the determinant of $B_{t+1}$ away from zero, which with the trace bound gives the uniform eigenvalue bounds of Lemma 3.1.
--
--   **Formalization Note** The paper's second line of (3.12) splits each factor as $\frac{y^Ts}{s^Ts}\cdot\frac{s^Ts}{s^TBs}$; that rearrangement is not restated.
-- source:
--   Byrd, Hansen, Nocedal, Singer, A Stochastic Quasi-Newton Method for Large-Scale Optimization, SIAM J. Optim. 26(2) (2016), p. 1016, Eq. (3.12) (citing Powell)

import Mathlib
import Definitions.Def_StochQuasiNewton_SQN_FiniteSum
import Definitions.Def_StochQuasiNewton_SQN_LBFGS

open scoped RealInnerProductSpace

namespace StochQuasiNewton.SQN

/-- Eq. (3.12), first line (Powell's determinant formula): under the hypotheses of (3.11), with
`m̃ = min t M` and `j_i = t − m̃ + i`,
`det(B_t^{(m̃)}) = det(B_t^{(0)}) ∏_{i=1}^{m̃} (y_{j_i}ᵀ s_{j_i}) / (s_{j_i}ᵀ B_t^{(i−1)} s_{j_i})`. -/
theorem lbfgs_det_formula {n N : ℕ} (f : Fin N → EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ∀ i, ContDiff ℝ 2 (f i)) (lam Lam : ℝ) (hlam : 0 < lam) (hLam : 0 < Lam) (bH : ℕ)
    (hbH : 1 ≤ bH)
    (hHess : ∀ SH : Finset (Fin N), SH.card = bH → ∀ w : EuclideanSpace ℝ (Fin n),
      StrictLoewnerBounds lam Lam (subsampledHessian f SH w))
    (M t : ℕ) (hM : 1 ≤ M) (ht : 1 ≤ t) (s y : ℕ → EuclideanSpace ℝ (Fin n))
    (hpairs : ∀ j, t - min t M < j → j ≤ t →
      s j ≠ 0 ∧ ∃ (SH : Finset (Fin N)) (wbar : EuclideanSpace ℝ (Fin n)),
        SH.card = bH ∧ y j = subsampledHessian f SH wbar (s j)) :
    (lbfgsDirectStage M t s y (min t M)).det =
      (lbfgsDirectStage M t s y 0).det *
        ∏ i ∈ Finset.Icc 1 (min t M),
          ⟪y (t - min t M + i), s (t - min t M + i)⟫ /
            dotProduct (s (t - min t M + i)).ofLp
              ((lbfgsDirectStage M t s y (i - 1)).mulVec (s (t - min t M + i)).ofLp) := by sorry

end StochQuasiNewton.SQN
