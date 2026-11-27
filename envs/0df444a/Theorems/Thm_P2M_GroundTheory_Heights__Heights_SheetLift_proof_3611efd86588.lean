-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetLift_proof_3611efd86588
-- name    : P2M_GroundTheory_Heights__Heights_SheetLift_proof_3611efd86588
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:39:10.404246+00:00
-- url     : https://prove2.me/theorems/dfe7a1aa-ae07-4d28-925e-c3abbbce252b
-- title:
--   P2 M Ground Theory Heights  Heights Sheet Lift proof 3611efd86588: P2 M Ground Theory Heights  Heights Sheet Lift proof 3611efd86588
-- statement:
--   The P2 M Ground Theory Heights  Heights Sheet Lift proof 3611efd86588 construction uses the P2 M Ground Theory Heights  Heights Sheet Lift proof 3611efd86588 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PSheetLift.lean#L86-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PSheetLift.lean#L86-L115

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

theorem P2M_GroundTheory_Heights__Heights_SheetLift_proof_3611efd86588 : SheetLift.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SheetLift».«proof» := P2M_GroundTheory_Heights__Heights_SheetLift_proof_3611efd86588
