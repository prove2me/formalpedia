-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_denseRange_completionEmbedding
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.denseRange_completionEmbedding
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:08:04.319224+00:00
-- url     : https://prove2.me/theorems/e291bfc3-716f-4316-874d-a1eef786f7e8
-- title:
--   Global Place: dense Range completion Embedding
-- statement:
--   The global function field is dense in each of its local completions.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Adeles/CompletedGlobalAdele.lean#L53-L57
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Adeles/CompletedGlobalAdele.lean#L53-L57

import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
import Mathlib.Topology.Algebra.Valued.ValuedField
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_Adele
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_CompletedGlobalAdele
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open Filter
open scoped RestrictedProduct WithZero
noncomputable section
open QEC.Coding.AlgebraicGeometry.GlobalPlace
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.denseRange_completionEmbedding (P : GlobalPlace k F) :
    DenseRange P.completionEmbedding := by sorry
