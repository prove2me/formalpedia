-- Prove2me | Theorems.Thm_RobustOpt2009_MatrixChance_bobkov_smooth_gaussian
-- name    : RobustOpt2009.MatrixChance.bobkov_smooth_gaussian
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-22T21:10:59.428784+00:00
-- url     : https://prove2.me/theorems/0471b013-2367-45d3-8c56-20220031c545
-- title:
--   Bobkov’s inequality for smooth Gaussian test functions
-- statement:
--   Let $f:\mathbb R^m\to[\eta,1-\eta]$ for $0<\eta\le 1/2$ have bounded first, second and third derivatives, with continuous third derivative. Let $\gamma_m$ be standard Gaussian measure and $I(p)=\varphi(\Phi^{-1}(p))$ the Gaussian isoperimetric profile. Then
--
--   $$I\left(\int f\,d\gamma_m\right)\le \int \sqrt{I(f)^2+\|\nabla f\|^2}\,d\gamma_m.$$
--
--   The smooth form suffices for proving Gaussian enlargement via approximations of distance functions.
-- source:
--   S. G. Bobkov, An isoperimetric inequality on the discrete cube, and an elementary proof of the isoperimetric inequality in Gauss space, Annals of Probability 25(1) (1997), Corollary 1, eq. (10), specialized to smooth bounded test functions. https://www-users.cse.umn.edu/~bobkov/papers/1997_AOP.pdf

import Definitions.Def_OAI_Probability_GaussianPropeller_Quantile

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators RealInnerProductSpace NNReal ENNReal

open OAI.GaussianPropeller.Quantile
variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "γ" => stdGaussian (EuclideanSpace ℝ (Fin m))

theorem RobustOpt2009.MatrixChance.bobkov_smooth_gaussian
    (f : E → ℝ) (g : E → E) (K : E → E →L[ℝ] E) (M : E → E →L[ℝ] (E →L[ℝ] E))
    (η Cg CK CM : ℝ) (hη_pos : 0 < η) (hη_le : η ≤ 1 - η)
    (hf_mem : ∀ x, f x ∈ Icc η (1 - η)) (hf_deriv : ∀ x, HasFDerivAt f (innerSL ℝ (g x)) x)
    (hg_deriv : ∀ x, HasFDerivAt g (K x) x) (hK_deriv : ∀ x, HasFDerivAt K (M x) x)
    (hM_cont : Continuous M) (hK_symm : ∀ x v w, ⟪K x v, w⟫ = ⟪v, K x w⟫)
    (hCg_nn : 0 ≤ Cg) (hCK_nn : 0 ≤ CK) (hCM_nn : 0 ≤ CM)
    (hg_bound : ∀ x, ‖g x‖ ≤ Cg) (hK_bound : ∀ x, ‖K x‖ ≤ CK) (hM_bound : ∀ x, ‖M x‖ ≤ CM) :
    I (∫ z, f z ∂γ) ≤ ∫ z, Real.sqrt (I (f z) ^ 2 + ‖g z‖ ^ 2) ∂γ := by sorry
