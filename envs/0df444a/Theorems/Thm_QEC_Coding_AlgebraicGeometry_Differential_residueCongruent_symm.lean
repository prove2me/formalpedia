-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_residueCongruent_symm
-- name    : QEC.Coding.AlgebraicGeometry.Differential.residueCongruent_symm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:18:40.799963+00:00
-- url     : https://prove2.me/theorems/99cdc42c-e42f-46ff-98dc-5faa4c074d87
-- title:
--   Differential: residue Congruent symm
-- statement:
--   The Differential construction uses the residue Congruent symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/DifferentialLocal.lean#L152-L158
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/DifferentialLocal.lean#L152-L158

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
open QEC.Coding.AlgebraicGeometry.Differential

theorem QEC.Coding.AlgebraicGeometry.Differential.residueCongruent_symm {P : GlobalPlace k F} {omega eta : Differential k F} :
    ResidueCongruent P omega eta -> ResidueCongruent P eta omega := by sorry
