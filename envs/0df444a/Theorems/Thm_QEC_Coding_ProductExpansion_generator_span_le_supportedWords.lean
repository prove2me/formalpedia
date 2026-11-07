-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_generator_span_le_supportedWords
-- name    : QEC.Coding.ProductExpansion.generator_span_le_supportedWords
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:31:09.320322+00:00
-- url     : https://prove2.me/theorems/fed8ed60-00f4-4707-8f90-e42cbaf92180
-- title:
--   Product Expansion: generator span le supported Words
-- statement:
--   The span of finitely many generators is supported inside their support
--   union.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L834-L846
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L834-L846

import Definitions.Def_QEC_Coding_Core_Definitions
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [Fintype R] [Fintype R']
omit [Fintype F] [Fintype R] [Fintype R']

theorem QEC.Coding.ProductExpansion.generator_span_le_supportedWords (C : Finset (Word F W)) :
    Submodule.span F (C : Set (Word F W)) ≤ supportedWords (generatorSupport C) := by sorry
