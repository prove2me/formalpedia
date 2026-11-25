-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_compAt_restrictTo_3d6cb5d193c4
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_compAt_restrictTo_3d6cb5d193c4
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:40:15.681674+00:00
-- url     : https://prove2.me/theorems/41a2d5de-def1-5582-a210-15369afa175e
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx comp At restrict To 3d6cb5d193c4: P2 M Ground Theory Heights  Heights Strong Approx comp At restrict To 3d6cb5d193c4
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx comp At restrict To 3d6cb5d193c4 construction uses the P2 M Ground Theory Heights  Heights Strong Approx comp At restrict To 3d6cb5d193c4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PTruncation.lean#L63-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PTruncation.lean#L63-L69

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

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_compAt_restrictTo_3d6cb5d193c4 (S : Finset (HeightOneSpectrum (𝓞 F))) (v : HeightOneSpectrum (𝓞 F))
    (a : AE F E) : compAt E v (restrictTo E S a) = if v ∈ S then compAt E v a else 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«compAt_restrictTo» := P2M_GroundTheory_Heights__Heights_StrongApprox_compAt_restrictTo_3d6cb5d193c4
