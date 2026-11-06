-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_galoisBaseSplitRationalPlace_injective
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.galoisBaseSplitRationalPlace_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:56:49.498397+00:00
-- url     : https://prove2.me/theorems/30831ff3-f6db-4085-99b7-ddc879aae998
-- title:
--   F256 Garcia Stichtenoth: galois Base Split Rational Place injective
-- statement:
--   Distinct split values give distinct actual rational places.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/GaloisBase.lean#L123-L132
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/GaloisBase.lean#L123-L132

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_BasePlaces
import Mathlib.Data.Fintype.EquivFin
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_GaloisBase
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.galoisBaseSplitRationalPlace_injective :
    Function.Injective galoisBaseSplitRationalPlace := by sorry
