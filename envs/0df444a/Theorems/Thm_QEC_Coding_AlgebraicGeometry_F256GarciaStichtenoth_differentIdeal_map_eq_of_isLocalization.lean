-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_differentIdeal_map_eq_of_isLocalization
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.differentIdeal_map_eq_of_isLocalization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:13:24.699946+00:00
-- url     : https://prove2.me/theorems/1f92627c-1ecc-43a2-a104-e3f4f28830ac
-- title:
--   F256 Garcia Stichtenoth: different Ideal map eq of is Localization
-- statement:
--   Simultaneous localization carries the global different ideal to the
--   different ideal of the localized finite extension.  The common fraction
--   fields make explicit that both pairs describe the same field extension.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differents/Localization.lean#L199-L233
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differents/Localization.lean#L199-L233

import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.Localization.NormTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differents_Localization
set_option autoImplicit false
open Module
open scoped nonZeroDivisors
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.differentIdeal_map_eq_of_isLocalization
    (R S Rm Sm K L : Type*)
    [CommRing R] [CommRing S] [CommRing Rm] [CommRing Sm]
    [IsDomain R] [IsDomain S] [IsDomain Rm] [IsDomain Sm]
    [Field K] [Field L]
    [Algebra R S] [Algebra R Rm] [Algebra S Sm]
    [Algebra R Sm] [Algebra Rm Sm]
    [IsScalarTower R S Sm] [IsScalarTower R Rm Sm]
    [Algebra R K] [Algebra Rm K]
    [Algebra S L] [Algebra Sm L] [Algebra K L]
    [Algebra R L] [Algebra Rm L]
    [IsScalarTower R K L] [IsScalarTower Rm K L]
    [IsScalarTower R S L] [IsScalarTower Rm Sm L]
    [IsScalarTower S Sm L] [IsScalarTower R Sm L]
    [IsFractionRing R K] [IsFractionRing Rm K]
    [IsFractionRing S L] [IsFractionRing Sm L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Module.Free R S] [Module.Finite R S]
    [Module.IsTorsionFree R S] [Module.IsTorsionFree Rm Sm]
    [Module.IsTorsionFree S Sm]
    [IsIntegrallyClosed R] [IsIntegrallyClosed Rm]
    [IsIntegralClosure S R L] [IsIntegralClosure Sm Rm L]
    [IsDedekindDomain S] [IsDedekindDomain Sm]
    (M : Submonoid R)
    [IsLocalization M Rm]
    [IsLocalization (Algebra.algebraMapSubmonoid S M) Sm]
    [IsLocalization (Algebra.algebraMapSubmonoid S R⁰) L]
    [IsLocalization (Algebra.algebraMapSubmonoid Sm Rm⁰) L] :
    Ideal.map (algebraMap S Sm) (differentIdeal R S) =
      differentIdeal Rm Sm := by sorry
