-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_singleV_tmul_ed4fb72a7896
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_singleV_tmul_ed4fb72a7896
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:57:22.031019+00:00
-- url     : https://prove2.me/theorems/b716b330-388f-4603-92d5-9b346128c803
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx Place Maps single V tmul ed4fb72a7896: P2 M Ground Theory Heights  Heights Strong Approx Place Maps single V tmul ed4fb72a7896
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx Place Maps single V tmul ed4fb72a7896 construction uses the P2 M Ground Theory Heights  Heights Strong Approx Place Maps single V tmul ed4fb72a7896 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PPlaceMaps.lean#L56-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PPlaceMaps.lean#L56-L57

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_PPlaceMaps
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_singleV_tmul_6c18ac5465de

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
open GroundTheory.Heights₂.Heights.StrongApprox
open Matrix NumberField IsDedekindDomain TensorProduct ReciprocityTheory.ChartRestriction.G.SA
open GroundTheory.Heights₂.Heights.StrongApprox.PlaceMaps
variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [Algebra F E]

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_singleV_tmul_ed4fb72a7896 (v : HeightOneSpectrum (𝓞 F)) (a : v.adicCompletion F) (b : E) :
    singleV E v (a ⊗ₜ b) = singleF F v a ⊗ₜ b := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«PlaceMaps».«singleV_tmul» := P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_singleV_tmul_ed4fb72a7896
