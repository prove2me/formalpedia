-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_PSL_isSimpleGroup
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.PSL_isSimpleGroup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:46:33.048751+00:00
-- url     : https://prove2.me/theorems/ce5bff34-8e00-4fc3-be50-24472f5405cb
-- title:
--   Cartwright Steger: PSL is Simple Group
-- statement:
--   The finite `PSL` endpoint is simple in the construction's ranks.  The
--   proof is an explicit Iwasawa argument: root subgroups are constructed above,
--   perfectness comes from elementary commutators, and the projective-action
--   kernel is proved to consist of scalar matrices.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Projective/SpecialLinear.lean#L541-L609
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Projective/SpecialLinear.lean#L541-L609

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_Congruence
import Mathlib.GroupTheory.GroupAction.Iwasawa
import Mathlib.GroupTheory.IsPerfect
import Mathlib.LinearAlgebra.Center
import Mathlib.LinearAlgebra.Projectivization.Action
import Mathlib.LinearAlgebra.Projectivization.Independence
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Projective_SpecialLinear
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open Matrix
open scoped commutatorElement
open scoped Pointwise
open scoped LinearAlgebra.Projectivization
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.PSL_isSimpleGroup
    (P : BasePrime) (r : Rank) (level : Nat) :
    IsSimpleGroup (PSL P r level) := by sorry
