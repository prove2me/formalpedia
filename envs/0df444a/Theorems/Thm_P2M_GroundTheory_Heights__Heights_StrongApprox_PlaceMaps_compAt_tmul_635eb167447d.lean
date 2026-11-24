-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_compAt_tmul_635eb167447d
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_compAt_tmul_635eb167447d
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:57:44.857394+00:00
-- url     : https://prove2.me/theorems/69b3d34b-8034-40e1-871b-6c2fc9f20dd4
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx Place Maps comp At tmul 635eb167447d: P2 M Ground Theory Heights  Heights Strong Approx Place Maps comp At tmul 635eb167447d
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx Place Maps comp At tmul 635eb167447d construction uses the P2 M Ground Theory Heights  Heights Strong Approx Place Maps comp At tmul 635eb167447d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PPlaceMaps.lean#L53-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PPlaceMaps.lean#L53-L54

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_PPlaceMaps
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_compAt_tmul_e1d8fccf6a3e

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

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_compAt_tmul_635eb167447d (v : HeightOneSpectrum (𝓞 F)) (a : FiniteAdeleRing (𝓞 F) F) (b : E) :
    compAt E v (a ⊗ₜ b) = evalAt F v a ⊗ₜ b := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«PlaceMaps».«compAt_tmul» := P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_compAt_tmul_635eb167447d
