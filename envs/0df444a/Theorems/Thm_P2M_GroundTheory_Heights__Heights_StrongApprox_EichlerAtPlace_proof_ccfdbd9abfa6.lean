-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerAtPlace_proof_ccfdbd9abfa6
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerAtPlace_proof_ccfdbd9abfa6
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:50:45.009937+00:00
-- url     : https://prove2.me/theorems/5c2b0b28-0f18-4e6d-9176-8777c02ea0d5
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx Eichler At Place proof ccfdbd9abfa6: P2 M Ground Theory Heights  Heights Strong Approx Eichler At Place proof ccfdbd9abfa6
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx Eichler At Place proof ccfdbd9abfa6 construction uses the P2 M Ground Theory Heights  Heights Strong Approx Eichler At Place proof ccfdbd9abfa6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PEichlerAtPlace.lean#L75-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PEichlerAtPlace.lean#L75-L92

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_PEichlerAtPlace
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

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerAtPlace_proof_ccfdbd9abfa6 (hPM : PlaceMaps.Statement) : EichlerAtPlace.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«EichlerAtPlace».«proof» := P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerAtPlace_proof_ccfdbd9abfa6
