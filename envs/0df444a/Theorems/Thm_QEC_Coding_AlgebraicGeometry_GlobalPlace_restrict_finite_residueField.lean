-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_restrict_finite_residueField
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.restrict_finite_residueField
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:12:34.44655+00:00
-- url     : https://prove2.me/theorems/482b4648-35c9-4578-ba7a-e546589997b9
-- title:
--   Global Place: restrict finite residue Field
-- statement:
--   A restricted place's residue field embeds into the actual ambient
--   residue field. In particular its finiteness is derived from the ambient
--   function field, not assumed separately for every coordinate window.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/NormalizedRestriction.lean#L121-L125
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/NormalizedRestriction.lean#L121-L125

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_GlobalPlace
import Mathlib.RingTheory.Valuation.Discrete.RankOne
import Mathlib.RingTheory.Valuation.IsTrivialOn
import Mathlib.FieldTheory.Finite.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_NormalizedRestriction
set_option autoImplicit false
open MonoidWithZeroHom
open scoped WithZero
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.GlobalPlace
noncomputable section
variable {k F E : Type*} [Field k] [Finite k] [Field F] [Field E]
    [Algebra k F] [Algebra k E] [Algebra F E]

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.restrict_finite_residueField [Algebra.IsAlgebraic F E]
    (Q : GlobalPlace k E) [Finite Q.residueField] :
    Finite (Q.restrict (F := F)).residueField := by sorry
