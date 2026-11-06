-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceSplitUpperHeightOne_injective
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSplitUpperHeightOne_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:33:23.809281+00:00
-- url     : https://prove2.me/theorems/76eba558-4f1d-4223-a1e5-521b55ad40d5
-- title:
--   F256 Garcia Stichtenoth: source Split Upper Height One injective
-- statement:
--   Distinct translations give distinct selected source height-one points.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceRationalSplitting.lean#L50-L59
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceRationalSplitting.lean#L50-L59

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSplittingIdeals
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceRationalSplitting
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSplitUpperHeightOne_injective
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (hsplit : galoisBaseWValue (Q.evaluateRegular x hregular) ≠ 0) :
    Function.Injective (sourceSplitUpperHeightOne Q P x hx) := by sorry
