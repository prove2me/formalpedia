-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_compAt_singleV_self_d2ccedef04de
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_compAt_singleV_self_d2ccedef04de
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:52:23.107909+00:00
-- url     : https://prove2.me/theorems/e1c987e6-a5f6-4cc3-987b-211cad145f68
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx Place Maps comp At single V self d2ccedef04de: P2 M Ground Theory Heights  Heights Strong Approx Place Maps comp At single V self d2ccedef04de
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx Place Maps comp At single V self d2ccedef04de construction uses the P2 M Ground Theory Heights  Heights Strong Approx Place Maps comp At single V self d2ccedef04de property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PPlaceMaps.lean#L65-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PPlaceMaps.lean#L65-L70

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

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_compAt_singleV_self_d2ccedef04de (v : HeightOneSpectrum (𝓞 F)) (x : Kv E v) :
    compAt E v (singleV E v x) = x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«PlaceMaps».«compAt_singleV_self» := P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_compAt_singleV_self_d2ccedef04de
