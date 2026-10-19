-- Prove2me | Theorems.Thm_TypeDensity_coeff_substAlgHom_kill
-- name    : TypeDensity.coeff_substAlgHom_kill
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:42.740065+00:00
-- url     : https://prove2.me/theorems/891508cc-6d1d-49a2-a93f-3dbc55d47080
-- title:
--   Coefficients of a substitution `T ↦ Y, X ↦ 0` (or `T ↦ 0, X ↦ Y`) into one-variable power series: the `n`-th coefficient is the coefficient of `Y^n` on the surviving axis `t`.
-- statement:
--   Coefficients of a substitution `T ↦ Y, X ↦ 0` (or `T ↦ 0, X ↦ Y`) into one-variable power series: the `n`-th coefficient is the coefficient of `Y^n` on the surviving axis `t`.
-- source:
--   TypeDensity/Surfaces/Lengths.lean#L506-L529

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Surfaces_Lengths
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.PicardGroup
set_option autoImplicit false

open TypeDensity

theorem TypeDensity.coeff_substAlgHom_kill (O : Type) [CommRing O] (f : Fin 2 → PowerSeries O)
    (hf : MvPowerSeries.HasSubst f) (s t : Fin 2) (hst : s ≠ t) (hs : f s = 0)
    (ht : f t = PowerSeries.X) (g : TwoSeries O) (n : ℕ) :
    PowerSeries.coeff n (MvPowerSeries.substAlgHom hf g) =
      MvPowerSeries.coeff (Finsupp.single t n) g := by sorry
