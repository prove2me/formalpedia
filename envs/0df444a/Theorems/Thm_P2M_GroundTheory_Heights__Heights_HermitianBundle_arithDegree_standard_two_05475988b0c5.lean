-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermitianBundle_arithDegree_standard_two_05475988b0c5
-- name    : P2M_GroundTheory_Heights__Heights_HermitianBundle_arithDegree_standard_two_05475988b0c5
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:14:06.815867+00:00
-- url     : https://prove2.me/theorems/807f536a-a9f2-420f-b80b-591d947eaa5e
-- title:
--   P2 M Ground Theory Heights  Heights Hermitian Bundle arith Degree standard two 05475988b0c5: P2 M Ground Theory Heights  Heights Hermitian Bundle arith Degree standard two 05475988b0c5
-- statement:
--   The P2 M Ground Theory Heights  Heights Hermitian Bundle arith Degree standard two 05475988b0c5 construction uses the P2 M Ground Theory Heights  Heights Hermitian Bundle arith Degree standard two 05475988b0c5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithDegreeExact.lean#L320-L322
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithDegreeExact.lean#L320-L322

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Slopes
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegreeExact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt Matrix
noncomputable section
variable {K : Type*} [Field K] [NumberField K]

theorem P2M_GroundTheory_Heights__Heights_HermitianBundle_arithDegree_standard_two_05475988b0c5 : (HermitianBundle.standard K 2).arithDegree = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HermitianBundle».«arithDegree_standard_two» := P2M_GroundTheory_Heights__Heights_HermitianBundle_arithDegree_standard_two_05475988b0c5
