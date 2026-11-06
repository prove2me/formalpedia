-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_multiplicity_map_eq_of_isLocalization
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.multiplicity_map_eq_of_isLocalization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:13:17.108196+00:00
-- url     : https://prove2.me/theorems/2c504bd2-d6ff-4d03-9724-72726b797656
-- title:
--   F256 Garcia Stichtenoth: multiplicity map eq of is Localization
-- statement:
--   Localization preserves the multiplicity of an ideal at a maximal ideal
--   which is disjoint from the localization monoid.  The proof contracts every
--   localized power of the maximal ideal; its positive powers are primary, so no
--   other prime factor of the ideal can affect the comparison.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differents/Localization.lean#L161-L194
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differents/Localization.lean#L161-L194

import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.Localization.NormTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differents_Localization
set_option autoImplicit false
open Module
open scoped nonZeroDivisors
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.multiplicity_map_eq_of_isLocalization
    (S Sm : Type*) [CommRing S] [CommRing Sm]
    [IsDomain S] [IsDomain Sm]
    [Algebra S Sm] [IsDedekindDomain S] [IsDedekindDomain Sm]
    (M : Submonoid S) [IsLocalization M Sm]
    (Q I : Ideal S) [Q.IsMaximal]
    (hQ : Disjoint (M : Set S) (Q : Set S)) :
    multiplicity (Ideal.map (algebraMap S Sm) Q)
        (Ideal.map (algebraMap S Sm) I) =
      multiplicity Q I := by sorry
