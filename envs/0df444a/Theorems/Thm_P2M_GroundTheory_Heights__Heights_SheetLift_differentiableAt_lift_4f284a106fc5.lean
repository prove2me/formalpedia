-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetLift_differentiableAt_lift_4f284a106fc5
-- name    : P2M_GroundTheory_Heights__Heights_SheetLift_differentiableAt_lift_4f284a106fc5
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:39:20.289942+00:00
-- url     : https://prove2.me/theorems/a53d30f2-99f6-5443-9fc0-bd667f633432
-- title:
--   P2 M Ground Theory Heights  Heights Sheet Lift differentiable At lift 4f284a106fc5: P2 M Ground Theory Heights  Heights Sheet Lift differentiable At lift 4f284a106fc5
-- statement:
--   The P2 M Ground Theory Heights  Heights Sheet Lift differentiable At lift 4f284a106fc5 construction uses the P2 M Ground Theory Heights  Heights Sheet Lift differentiable At lift 4f284a106fc5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PSheetLift.lean#L73-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PSheetLift.lean#L73-L84

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StSheetLift
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSheetLift
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_eval_bsmul_of_isMultiHomog
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_prod_update_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Filter Topology MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiHomogIdeal mcPts segre IsSheet bsmul eval_bsmul_of_isMultiHomog
  prod_update_eq)
open GroundTheory.Heights₂.Heights.SheetLift
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
omit [Fintype K] [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_SheetLift_differentiableAt_lift_4f284a106fc5 [DecidableEq K] {e : ℕ} (i0 : (k : K) → ι k) (k0 : K)
    {h : (Fin e → ℂ) → ((k : K) → ι k) → ℂ} {y : Fin e → ℂ} (hd : DifferentiableAt ℂ h y)
    (hne : h y i0 ≠ 0) : DifferentiableAt ℂ (fun y' => lift i0 k0 (h y')) y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SheetLift».«differentiableAt_lift» := P2M_GroundTheory_Heights__Heights_SheetLift_differentiableAt_lift_4f284a106fc5
