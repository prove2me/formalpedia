-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_AETopologicalRing_linearIndependent_one_anti_66bff719bdbc
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_AETopologicalRing_linearIndependent_one_anti_66bff719bdbc
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:39:08.792126+00:00
-- url     : https://prove2.me/theorems/2adf2460-8e4c-4bfe-96a8-79113b8b406e
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx AETopological Ring linear Independent one anti 66bff719bdbc: P2 M Ground Theory Heights  Heights Strong Approx AETopological Ring linear Independent o
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx AETopological Ring linear Independent one anti 66bff719bdbc construction uses the P2 M Ground Theory Heights  Heights Strong Approx AETopological Ring linear Independent one anti 66bff719bdbc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PAETopologicalRing.lean#L45-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PAETopologicalRing.lean#L45-L58

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_PAETopologicalRing
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
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
omit [NumberField F]

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_AETopologicalRing_linearIndependent_one_anti_66bff719bdbc (c : E ≃ₐ[F] E) {δ : E} (hδ : c δ = -δ)
    (h0 : δ ≠ 0) : LinearIndependent F ![(1 : E), δ] := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«AETopologicalRing».«linearIndependent_one_anti» := P2M_GroundTheory_Heights__Heights_StrongApprox_AETopologicalRing_linearIndependent_one_anti_66bff719bdbc
