-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermitianBundle_degree_top_eq_arithDegree_8d3e6fe17684
-- name    : P2M_GroundTheory_Heights__Heights_HermitianBundle_degree_top_eq_arithDegree_8d3e6fe17684
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:18:19.036919+00:00
-- url     : https://prove2.me/theorems/40fc9ef9-8c68-4da3-ae06-73c8058a8c4d
-- title:
--   P2 M Ground Theory Heights  Heights Hermitian Bundle degree top eq arith Degree 8d3e6fe17684: P2 M Ground Theory Heights  Heights Hermitian Bundle degree top eq arith Degree 8d3e6fe17684
-- statement:
--   The P2 M Ground Theory Heights  Heights Hermitian Bundle degree top eq arith Degree 8d3e6fe17684 construction uses the P2 M Ground Theory Heights  Heights Hermitian Bundle degree top eq arith Degree 8d3e6fe17684 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/DegreeTopEqArithDegree.lean#L11-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/DegreeTopEqArithDegree.lean#L11-L27

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_LinearIndependentSumElimOfExact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_DegreeTopEqArithDegree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_HermitianBundle_degree_top_eq_arithDegree_8d3e6fe17684 {K : Type*} [Field K] [NumberField K]
    (E : HermitianBundle K) : E.degree ⊤ = E.arithDegree := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HermitianBundle».«degree_top_eq_arithDegree» := P2M_GroundTheory_Heights__Heights_HermitianBundle_degree_top_eq_arithDegree_8d3e6fe17684
