-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_compAt_singleV_ne_7a445a49239f
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_compAt_singleV_ne_7a445a49239f
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:45.883317+00:00
-- url     : https://prove2.me/theorems/cdfd7619-5eee-4f5d-940e-463545025e47
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx Place Maps comp At single V ne 7a445a49239f: P2 M Ground Theory Heights  Heights Strong Approx Place Maps comp At single V ne 7a445a49239f
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx Place Maps comp At single V ne 7a445a49239f construction uses the P2 M Ground Theory Heights  Heights Strong Approx Place Maps comp At single V ne 7a445a49239f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PPlaceMaps.lean#L72-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PPlaceMaps.lean#L72-L77

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

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_compAt_singleV_ne_7a445a49239f {v w : HeightOneSpectrum (𝓞 F)} (h : w ≠ v) (x : Kv E v) :
    compAt E w (singleV E v x) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«PlaceMaps».«compAt_singleV_ne» := P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_compAt_singleV_ne_7a445a49239f
