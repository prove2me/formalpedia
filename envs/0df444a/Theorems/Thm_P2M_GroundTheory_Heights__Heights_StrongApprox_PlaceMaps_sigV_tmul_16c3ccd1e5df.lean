-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_sigV_tmul_16c3ccd1e5df
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_sigV_tmul_16c3ccd1e5df
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:52.623829+00:00
-- url     : https://prove2.me/theorems/22b691e1-17fe-4aa3-bec2-cdd2cecbcc68
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx Place Maps sig V tmul 16c3ccd1e5df: P2 M Ground Theory Heights  Heights Strong Approx Place Maps sig V tmul 16c3ccd1e5df
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx Place Maps sig V tmul 16c3ccd1e5df construction uses the P2 M Ground Theory Heights  Heights Strong Approx Place Maps sig V tmul 16c3ccd1e5df property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PPlaceMaps.lean#L62-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PPlaceMaps.lean#L62-L63

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

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_sigV_tmul_16c3ccd1e5df (c : E ≃ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (a : v.adicCompletion F) (b : E) :
    sigV c v (a ⊗ₜ b) = a ⊗ₜ c b := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«PlaceMaps».«sigV_tmul» := P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_sigV_tmul_16c3ccd1e5df
