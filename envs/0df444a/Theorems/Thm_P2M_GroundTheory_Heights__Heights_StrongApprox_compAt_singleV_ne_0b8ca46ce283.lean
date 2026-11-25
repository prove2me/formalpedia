-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_compAt_singleV_ne_0b8ca46ce283
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_compAt_singleV_ne_0b8ca46ce283
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:39:43.808394+00:00
-- url     : https://prove2.me/theorems/ced3d5be-1ade-58e0-83ea-1551d289c75b
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx comp At single V ne 0b8ca46ce283: P2 M Ground Theory Heights  Heights Strong Approx comp At single V ne 0b8ca46ce283
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx comp At single V ne 0b8ca46ce283 construction uses the P2 M Ground Theory Heights  Heights Strong Approx comp At single V ne 0b8ca46ce283 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PTruncation.lean#L56-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PTruncation.lean#L56-L61

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_PTruncation
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
open Matrix NumberField IsDedekindDomain TensorProduct Topology ReciprocityTheory.ChartRestriction.G.SA
open Classical
variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [Algebra F E]

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_compAt_singleV_ne_0b8ca46ce283 {u v : HeightOneSpectrum (𝓞 F)} (h : u ≠ v) (x : Kv E v) :
    compAt E u (singleV E v x) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«compAt_singleV_ne» := P2M_GroundTheory_Heights__Heights_StrongApprox_compAt_singleV_ne_0b8ca46ce283
