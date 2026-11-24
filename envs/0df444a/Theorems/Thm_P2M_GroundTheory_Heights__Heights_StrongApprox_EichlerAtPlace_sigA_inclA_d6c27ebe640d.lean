-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerAtPlace_sigA_inclA_d6c27ebe640d
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerAtPlace_sigA_inclA_d6c27ebe640d
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:58:37.6348+00:00
-- url     : https://prove2.me/theorems/175bf5c9-28fc-480f-bc5e-3cd7fd8ca877
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx Eichler At Place sig A incl A d6c27ebe640d: P2 M Ground Theory Heights  Heights Strong Approx Eichler At Place sig A incl A d6c27ebe640d
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx Eichler At Place sig A incl A d6c27ebe640d construction uses the P2 M Ground Theory Heights  Heights Strong Approx Eichler At Place sig A incl A d6c27ebe640d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PEichlerAtPlace.lean#L21-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PEichlerAtPlace.lean#L21-L22

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_PEichlerAtPlace
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_sigA_inclA_87fddbe307ad

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

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerAtPlace_sigA_inclA_d6c27ebe640d (c : E ≃ₐ[F] E) (x : E) : sigA c (inclA F E x) = inclA F E (c x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«EichlerAtPlace».«sigA_inclA» := P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerAtPlace_sigA_inclA_d6c27ebe640d
