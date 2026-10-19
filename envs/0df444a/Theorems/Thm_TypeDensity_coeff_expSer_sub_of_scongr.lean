-- Prove2me | Theorems.Thm_TypeDensity_coeff_expSer_sub_of_scongr
-- name    : TypeDensity.coeff_expSer_sub_of_scongr
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:19:55.477303+00:00
-- url     : https://prove2.me/theorems/4eb87cd6-013e-4226-8411-b70cb64ddb26
-- title:
--   If `f ≡ g` through degree `n - 1`, then the degree-`n` discrepancy of `exp f` and `exp g` equals that of `f` and `g`.
-- statement:
--   If `f ≡ g` through degree `n - 1`, then the degree-`n` discrepancy of `exp f` and `exp g` equals that of `f` and `g`.
-- source:
--   TypeDensity/Reciprocity/Defs.lean#L527-L535

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

theorem TypeDensity.coeff_expSer_sub_of_scongr (n : ℕ) (hn : 0 < n) (f g : Ser)
    (hf : PowerSeries.constantCoeff f = 0) (hg : PowerSeries.constantCoeff g = 0)
    (h : SCongr (n - 1) f g) :
    PowerSeries.coeff n (expSer f) - PowerSeries.coeff n (expSer g) =
      PowerSeries.coeff n f - PowerSeries.coeff n g := by sorry
