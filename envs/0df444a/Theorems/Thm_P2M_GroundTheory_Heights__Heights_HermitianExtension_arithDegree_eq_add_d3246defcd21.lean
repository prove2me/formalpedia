-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermitianExtension_arithDegree_eq_add_d3246defcd21
-- name    : P2M_GroundTheory_Heights__Heights_HermitianExtension_arithDegree_eq_add_d3246defcd21
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:21:36.907141+00:00
-- url     : https://prove2.me/theorems/15fafd10-d8ae-4716-bdd1-9bfe8c97b332
-- title:
--   P2 M Ground Theory Heights  Heights Hermitian Extension arith Degree eq add d3246defcd21: P2 M Ground Theory Heights  Heights Hermitian Extension arith Degree eq add d3246defcd21
-- statement:
--   The P2 M Ground Theory Heights  Heights Hermitian Extension arith Degree eq add d3246defcd21 construction uses the P2 M Ground Theory Heights  Heights Hermitian Extension arith Degree eq add d3246defcd21 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithDegreeExact.lean#L290-L313
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithDegreeExact.lean#L290-L313

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
open GroundTheory.Heights₂.Heights.HermitianExtension
variable {E' E E'' : HermitianBundle K} (X : HermitianExtension E' E E'')
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
include X

theorem P2M_GroundTheory_Heights__Heights_HermitianExtension_arithDegree_eq_add_d3246defcd21 : E.arithDegree = E'.arithDegree + E''.arithDegree := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HermitianExtension».«arithDegree_eq_add» := P2M_GroundTheory_Heights__Heights_HermitianExtension_arithDegree_eq_add_d3246defcd21
