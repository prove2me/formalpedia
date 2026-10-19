-- Prove2me | Theorems.Thm_TypeDensity_coeff_logSer_sub_of_scongr
-- name    : TypeDensity.coeff_logSer_sub_of_scongr
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:19:50.233418+00:00
-- url     : https://prove2.me/theorems/b459e2bb-8b00-4040-9dad-be479bb0ab1a
-- title:
--   If `u ≡ v` through degree `n - 1`, then the degree-`n` discrepancy of `log u` and `log v` equals that of `u` and `v`.
-- statement:
--   If `u ≡ v` through degree `n - 1`, then the degree-`n` discrepancy of `log u` and `log v` equals that of `u` and `v`.
-- source:
--   TypeDensity/Reciprocity/Defs.lean#L537-L547

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Theorems.Thm_TypeDensity_coeff_subst_sub
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Log
set_option autoImplicit false

open TypeDensity

theorem TypeDensity.coeff_logSer_sub_of_scongr (n : ℕ) (hn : 0 < n) (u v : Ser)
    (hu : PowerSeries.constantCoeff u = 1) (hv : PowerSeries.constantCoeff v = 1)
    (huv : SCongr (n - 1) u v) :
    PowerSeries.coeff n (logSer u) - PowerSeries.coeff n (logSer v) =
      PowerSeries.coeff n u - PowerSeries.coeff n v := by sorry
