-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_compAt_inclA_b8a4d4babfbf
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_compAt_inclA_b8a4d4babfbf
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:41.480137+00:00
-- url     : https://prove2.me/theorems/6aa10159-864a-4bf1-982d-7654ec375226
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx Place Maps comp At incl A b8a4d4babfbf: P2 M Ground Theory Heights  Heights Strong Approx Place Maps comp At incl A b8a4d4babfbf
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx Place Maps comp At incl A b8a4d4babfbf construction uses the P2 M Ground Theory Heights  Heights Strong Approx Place Maps comp At incl A b8a4d4babfbf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PPlaceMaps.lean#L129-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PPlaceMaps.lean#L129-L132

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_PPlaceMaps
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

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_compAt_inclA_b8a4d4babfbf (v : HeightOneSpectrum (𝓞 F)) (x : E) :
    compAt E v (inclA F E x) = inclV E v x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«PlaceMaps».«compAt_inclA» := P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_compAt_inclA_b8a4d4babfbf
