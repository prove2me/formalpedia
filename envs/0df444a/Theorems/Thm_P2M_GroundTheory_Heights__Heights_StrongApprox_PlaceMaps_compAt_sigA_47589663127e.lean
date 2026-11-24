-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_compAt_sigA_47589663127e
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_compAt_sigA_47589663127e
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:54.892106+00:00
-- url     : https://prove2.me/theorems/b10e16bf-7fbc-42d9-8009-e890a19381a9
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx Place Maps comp At sig A 47589663127e: P2 M Ground Theory Heights  Heights Strong Approx Place Maps comp At sig A 47589663127e
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx Place Maps comp At sig A 47589663127e construction uses the P2 M Ground Theory Heights  Heights Strong Approx Place Maps comp At sig A 47589663127e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PPlaceMaps.lean#L122-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PPlaceMaps.lean#L122-L127

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

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_compAt_sigA_47589663127e (c : E ≃ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (a : AE F E) :
    compAt E v (sigA c a) = sigV c v (compAt E v a) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«PlaceMaps».«compAt_sigA» := P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_compAt_sigA_47589663127e
