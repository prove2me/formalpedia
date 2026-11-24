-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermitianBundle_degree_eq_arithDegree_1ab30fd3c0e4
-- name    : P2M_GroundTheory_Heights__Heights_HermitianBundle_degree_eq_arithDegree_1ab30fd3c0e4
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:02:23.473163+00:00
-- url     : https://prove2.me/theorems/f5a473f8-a183-4b47-8cbf-e2aa7bd4a5d6
-- title:
--   P2 M Ground Theory Heights  Heights Hermitian Bundle degree eq arith Degree 1ab30fd3c0e4: P2 M Ground Theory Heights  Heights Hermitian Bundle degree eq arith Degree 1ab30fd3c0e4
-- statement:
--   The P2 M Ground Theory Heights  Heights Hermitian Bundle degree eq arith Degree 1ab30fd3c0e4 construction uses the P2 M Ground Theory Heights  Heights Hermitian Bundle degree eq arith Degree 1ab30fd3c0e4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithDegreeIdeal.lean#L140-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithDegreeIdeal.lean#L140-L161

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegreeExact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegreeIdeal
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
open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt Matrix
noncomputable section
variable {K : Type*} [Field K] [NumberField K]

theorem P2M_GroundTheory_Heights__Heights_HermitianBundle_degree_eq_arithDegree_1ab30fd3c0e4 (E : HermitianBundle K)
    (F : Submodule (𝓞 K) E.carrier) :
    E.degree F = GroundTheory.Heights₂.Heights.arithDegree (E.metric.comap F.subtype F.injective_subtype) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HermitianBundle».«degree_eq_arithDegree» := P2M_GroundTheory_Heights__Heights_HermitianBundle_degree_eq_arithDegree_1ab30fd3c0e4
