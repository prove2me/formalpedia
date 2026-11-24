-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerDense_c_invol_cedc9596829d
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerDense_c_invol_cedc9596829d
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:52:51.261565+00:00
-- url     : https://prove2.me/theorems/c512a51b-c2c4-41b9-85e5-73eac306be64
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx Eichler Dense c invol cedc9596829d: P2 M Ground Theory Heights  Heights Strong Approx Eichler Dense c invol cedc9596829d
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx Eichler Dense c invol cedc9596829d construction uses the P2 M Ground Theory Heights  Heights Strong Approx Eichler Dense c invol cedc9596829d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PEichlerDense.lean#L97-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PEichlerDense.lean#L97-L109

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_PEichlerDense
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
open GroundTheory.Heights₂.Heights.StrongApprox.EichlerDense
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerDense_c_invol_cedc9596829d (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1) (x : E) :
    c (c x) = x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«EichlerDense».«c_invol» := P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerDense_c_invol_cedc9596829d
