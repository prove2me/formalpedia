-- Prove2me | Theorems.Thm_TypeDensity_coeff_subst_sub
-- name    : TypeDensity.coeff_subst_sub
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:01:53.834992+00:00
-- url     : https://prove2.me/theorems/67145d3e-86e3-4f57-b207-9e51c3f3a2c0
-- title:
--   coeff subst sub
-- statement:
--   If `n > 0`, `f` and `g` have zero constant term and agree in all degrees `< n`, then for every series `P` the difference of the `n`-th coefficients of `P(f)` and `P(g)` equals `P₁ · (fₙ - gₙ)`, where `P₁` is the linear coefficient of `P`.
-- source:
--   TypeDensity/Reciprocity/Defs.lean#L515-L525

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Theorems.Thm_TypeDensity_coeff_subst_eq_sum
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

theorem TypeDensity.coeff_subst_sub (n : ℕ) (hn : 0 < n) (P f g : Ser)
    (hf : PowerSeries.constantCoeff f = 0) (hg : PowerSeries.constantCoeff g = 0)
    (h : SCongr (n - 1) f g) :
    PowerSeries.coeff n (P.subst f) - PowerSeries.coeff n (P.subst g) =
      PowerSeries.coeff 1 P • (PowerSeries.coeff n f - PowerSeries.coeff n g) := by sorry
