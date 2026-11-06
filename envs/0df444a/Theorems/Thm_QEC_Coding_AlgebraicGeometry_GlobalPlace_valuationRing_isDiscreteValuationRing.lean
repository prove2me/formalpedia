-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_valuationRing_isDiscreteValuationRing
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.valuationRing_isDiscreteValuationRing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:12:25.337284+00:00
-- url     : https://prove2.me/theorems/a57b5067-cc99-4c6c-8c93-993051f57dee
-- title:
--   Global Place: valuation Ring is Discrete Valuation Ring
-- statement:
--   The valuation ring of a global place is a discrete valuation ring.  The
--   cyclicity and nontriviality instances used here are local to this proof.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/DifferentialLocal.lean#L186-L191
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/DifferentialLocal.lean#L186-L191

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_Differential
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_GlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RationalPlace
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Valuation.Discrete.RankOne
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_DifferentialLocal
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped WithZero
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
open QEC.Coding.AlgebraicGeometry.GlobalPlace

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.valuationRing_isDiscreteValuationRing (P : GlobalPlace k F) :
    IsDiscreteValuationRing P.valuationRing := by sorry
