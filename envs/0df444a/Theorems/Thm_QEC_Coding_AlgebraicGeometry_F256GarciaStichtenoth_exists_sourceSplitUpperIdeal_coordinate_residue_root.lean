-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_exists_sourceSplitUpperIdeal_coordinate_residue_root
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.exists_sourceSplitUpperIdeal_coordinate_residue_root
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:00:45.527206+00:00
-- url     : https://prove2.me/theorems/fca83a3e-6cea-43dc-9a26-96de4aecd362
-- title:
--   F256 Garcia Stichtenoth: exists source Split Upper Ideal coordinate residue root
-- statement:
--   Modulo every upper prime, the integral source coordinate is one of the
--   sixteen constructed constant roots.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceSplitIntegralClosure.lean#L311-L380
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceSplitIntegralClosure.lean#L311-L380

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSplitAlgebra
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSplitIntegralClosure
set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.exists_sourceSplitUpperIdeal_coordinate_residue_root
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (hsplit : galoisBaseWValue (Q.evaluateRegular x hregular) ≠ 0)
    (R : Ideal (SourceSplitIntegralClosure Q P x hx)) [R.IsMaximal]
    [R.LiesOver (IsLocalRing.maximalIdeal Q.place.valuationRing)] :
    ∃ b ∈ sourceStepArtinSchreierRoots
        (⟨Q.evaluateRegular x hregular, hsplit⟩ : GaloisBaseSplitPoint),
      sourceSplitIntegralCoordinate Q P x hx hregular hsplit -
          algebraMap Q.place.valuationRing
            (SourceSplitIntegralClosure Q P x hx)
            (GlobalPlace.constantsToValuationRing Q.place b) ∈ R := by sorry
