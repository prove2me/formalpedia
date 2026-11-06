-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_completionEmbedding_injective
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.completionEmbedding_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:08:05.082201+00:00
-- url     : https://prove2.me/theorems/e8096ff2-5966-4641-b6d0-0c26c98d6a0f
-- title:
--   Global Place: completion Embedding injective
-- statement:
--   The canonical map into a local completion loses no global function.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Adeles/CompletedGlobalAdele.lean#L60-L62
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Adeles/CompletedGlobalAdele.lean#L60-L62

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

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.completionEmbedding_injective (P : GlobalPlace k F) :
    Function.Injective P.completionEmbedding := by sorry
