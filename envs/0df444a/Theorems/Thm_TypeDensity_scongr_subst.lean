-- Prove2me | Theorems.Thm_TypeDensity_scongr_subst
-- name    : TypeDensity.scongr_subst
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:31:48.641985+00:00
-- url     : https://prove2.me/theorems/4544e760-0880-451b-84d9-e2538ce1676d
-- title:
--   scongr subst
-- statement:
--   Substitution preserves congruence of series: if `f` and `g` have zero constant term and agree in all degrees `≤ n`, then `a(f)` and `a(g)` agree in all degrees `≤ n` for every series `a`.
-- source:
--   TypeDensity/Reciprocity/Quantum.lean#L886-L905

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
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

theorem TypeDensity.scongr_subst (n : ℕ) (a : Ser) (f g : Ser)
    (hf : PowerSeries.constantCoeff f = 0) (hg : PowerSeries.constantCoeff g = 0)
    (h : SCongr n f g) : SCongr n (a.subst f) (a.subst g) := by sorry
