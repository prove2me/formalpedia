-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_exists_splitUpperIdeal_auxiliary_residue_root
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.exists_splitUpperIdeal_auxiliary_residue_root
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:58:07.234878+00:00
-- url     : https://prove2.me/theorems/006e3d42-6292-4228-aa8f-a2082d7d87fa
-- title:
--   F256 Garcia Stichtenoth: exists split Upper Ideal auxiliary residue root
-- statement:
--   Modulo every upper prime, the integral auxiliary coordinate equals one of
--   the sixteen concrete constant roots of the residual polynomial.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SplitIntegralClosure.lean#L206-L276
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SplitIntegralClosure.lean#L206-L276

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ResidualPolynomial
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SplitIntegralClosure
set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.exists_splitUpperIdeal_auxiliary_residue_root
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (R : Ideal (SplitIntegralClosure Q P x hx)) [R.IsMaximal]
    [R.LiesOver (IsLocalRing.maximalIdeal Q.place.valuationRing)] :
    ∃ b ∈ f256ArtinSchreierRoots (Q.evaluateRegular x hregular),
      splitIntegralAuxiliaryCoordinate Q P x hx hregular -
          algebraMap Q.place.valuationRing (SplitIntegralClosure Q P x hx)
            (GlobalPlace.constantsToValuationRing Q.place b) ∈ R := by sorry
