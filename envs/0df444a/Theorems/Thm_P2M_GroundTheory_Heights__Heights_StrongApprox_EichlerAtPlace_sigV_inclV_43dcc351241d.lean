-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerAtPlace_sigV_inclV_43dcc351241d
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerAtPlace_sigV_inclV_43dcc351241d
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:58:49.256864+00:00
-- url     : https://prove2.me/theorems/c6c75799-a70d-4711-9b59-9e5bb6de94c3
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx Eichler At Place sig V incl V 43dcc351241d: P2 M Ground Theory Heights  Heights Strong Approx Eichler At Place sig V incl V 43dcc351241d
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx Eichler At Place sig V incl V 43dcc351241d construction uses the P2 M Ground Theory Heights  Heights Strong Approx Eichler At Place sig V incl V 43dcc351241d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PEichlerAtPlace.lean#L17-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PEichlerAtPlace.lean#L17-L19

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_PEichlerAtPlace
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_sigV_inclV_8ef6594cc226

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
open GroundTheory.Heights₂.Heights.StrongApprox.EichlerAtPlace
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerAtPlace_sigV_inclV_43dcc351241d (c : E ≃ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (x : E) :
    sigV c v (inclV E v x) = inclV E v (c x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«EichlerAtPlace».«sigV_inclV» := P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerAtPlace_sigV_inclV_43dcc351241d
