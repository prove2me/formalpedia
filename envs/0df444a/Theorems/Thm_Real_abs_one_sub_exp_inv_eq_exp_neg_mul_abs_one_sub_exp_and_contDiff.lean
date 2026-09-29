-- Prove2me | Theorems.Thm_Real_abs_one_sub_exp_inv_eq_exp_neg_mul_abs_one_sub_exp_and_contDiff
-- name    : Real.abs_one_sub_exp_inv_eq_exp_neg_mul_abs_one_sub_exp_and_contDiff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/520857bc-45bf-5cb1-99ec-1a2d5961dc63
-- title:
--   Absolute value of 1-(± e^X)⁻¹ in exponential coordinates
-- statement:
--   The theorem is a conjunction of four hypothesis-free elementary assertions about the real exponential. First, for every real $X$ one has $|1-(e^X)^{-1}| = e^{-X}\,|1-e^X|$, so that the absolute value of $1-y^{-1}$ at a positive real $y=e^X$ factors as the decaying weight $e^{-X}$ times $|1-e^X|$. Second, for every real $X$ one has $|1-(-e^X)^{-1}| = 1+e^{-X}$; the inverse of a negative real $-e^X$ contributes with the opposite sign, so no absolute value remains on the right. Third, for every real $X$ the quantity $1+e^{-X}$ is strictly positive. Fourth, the function $X \mapsto 1+e^{-X}$ on $\mathbb{R}$ is $C^\infty$ (continuously differentiable of order $\top$ in $\mathbb{N}_\infty$) as a map of real normed spaces. All four claims are stated for all real $X$ with no side conditions.
--
--   This is the elementary computation that describes, in the exponential coordinate $y = s\,e^{X}$ with sign $s = \pm 1$ on a real archimedean coordinate, the behaviour of the factor $|1-y^{-1}|$: for $s=+1$ it is a smooth positive weight times the kink $|1-e^{X}|$ at $X=0$, while for $s=-1$ it is itself a smooth positive function. It is used in the analysis of archimedean discrepancy factors, being cited by [`NumberField.exists_addSubgroup_forall_finsum_units_mul_prod_zpow_neg_mul_sum_integral_discWindow_eq_tsum_mul_tsum_ite_kinkWindow_of_contDiff_of_forall_eq_of_norm_sub_le`](thm.html#NumberField.exists_addSubgroup_forall_finsum_units_mul_prod_zpow_neg_mul_sum_integral_discWindow_eq_tsum_mul_tsum_ite_kinkWindow_of_contDiff_of_forall_eq_of_norm_sub_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Real_abs_one_sub_exp_inv_eq_exp_neg_mul_abs_one_sub_exp_and_contDiff.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Real.abs_one_sub_exp_inv_eq_exp_neg_mul_abs_one_sub_exp_and_contDiff :
    (∀ X : ℝ, |1 - (Real.exp X)⁻¹| = Real.exp (-X) * |1 - Real.exp X|) ∧
    (∀ X : ℝ, |1 - (-Real.exp X)⁻¹| = 1 + Real.exp (-X)) ∧
    (∀ X : ℝ, 0 < 1 + Real.exp (-X)) ∧
    ContDiff ℝ (⊤ : ℕ∞) (fun X : ℝ => 1 + Real.exp (-X)) := by sorry
