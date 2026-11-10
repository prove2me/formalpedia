-- Prove2me | Theorems.Thm_PrivateAgnosticHalfspace_Gaussian_lemma_B_10
-- name    : PrivateAgnosticHalfspace.Gaussian.lemma_B_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T11:25:04.346393+00:00
-- url     : https://prove2.me/theorems/3c57efb3-12af-4d28-b6b4-a6467a8601d8
-- title:
--   Lemma B.10 — unit-norm halfspace approximation
-- statement:
--   There is one universal $C>0$ such that, for every dimension $d\ge1$, accuracy $\alpha\in(0,1)$ and affine halfspace $c(x)=\operatorname{sign}(\langle w,x\rangle+t)$, there are an integer $p\ge0$ and coefficients $v$ in the degree-$p$ normalized tensor Hermite basis with
--   $$
--   p\le C\alpha^{-2},\qquad \|v\|_2\le1,\qquad
--   \int_{\mathbb R^d}\left|c(x)-\sum_{|\kappa|\le p}v_\kappa h_\kappa(x)\right|\,dN(0,I_d)(x)\le\alpha.
--   $$
--   Both biased and constant halfspaces are included, and the approximation error is integrable. The universal constant is chosen before the dimension, accuracy and halfspace.
--
--   This justifies the learner's compact unit coefficient ball without restricting the comparison class.
--
--   Differences from the source:
--   - encoding: real ±1 halfspace values and a Gaussian L¹ norm → Bool halfspaces decoded to ±1, an explicit finite Hermite vector and an integrable absolute-error integral; reason: preserves all affine halfspaces, including zero normals and constant classifiers; sign(0)=+1 is fixed
-- source:
--   Giorgio Racca, Amartya Sanyal, Vikrant Singhal, STOC 2027 submission #1006 (October 2026), p. 22–23, Lemma B.10; canonical PDF sha256 f0122a33e29daa624b530bdd0b071998d8e44197b30449b0cb3213289645cec7

import Definitions.Def_PrivateAgnosticHalfspace_Gaussian_Regression

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
set_option autoImplicit false

namespace PrivateAgnosticHalfspace.Gaussian

theorem lemma_B_10 :
    ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ), 1 ≤ d → ∀ (α : ℝ), 0 < α ∧ α < 1 →
      ∀ (w : Vec d) (t : ℝ), ∃ (p : ℕ) (v : Coeff d p),
        (p : ℝ) ≤ C / α ^ 2 ∧ ‖v‖ ≤ 1 ∧
        Integrable (fun x => |label (affine d w t x) - polynomialPredictor d p v x|) (gaussian d) ∧
        (∫ x, |label (affine d w t x) - polynomialPredictor d p v x| ∂gaussian d) ≤ α := by sorry

end PrivateAgnosticHalfspace.Gaussian
