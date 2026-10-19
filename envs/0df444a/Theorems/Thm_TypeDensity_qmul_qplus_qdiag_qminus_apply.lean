-- Prove2me | Theorems.Thm_TypeDensity_qmul_qplus_qdiag_qminus_apply
-- name    : TypeDensity.qmul_qplus_qdiag_qminus_apply
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:02:20.356426+00:00
-- url     : https://prove2.me/theorems/395e7bb9-e84f-4126-88d4-8cfc70db196d
-- title:
--   Expansion of the coefficient `(ι₊(A) · qdiag(D) · ι₋(C))_{c,h}` as a triple sum.
-- statement:
--   This gives the expansion of the coefficient `(ι₊(A) · qdiag(D) · ι₋(C))_{c,h}` as a triple sum.
-- source:
--   TypeDensity/Reciprocity/Defs.lean#L956-L1015

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Theorems.Thm_TypeDensity_qpow_add
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

theorem TypeDensity.qmul_qplus_qdiag_qminus_apply (A Cq : QSer) (D : Ser) (c h : ℕ) :
    qmul (qmul (qplus A) (qdiag D)) (qminus Cq) c h =
      ∑ rx ∈ Finset.range (c + 1), ∑ m ∈ Finset.range (c + 1), ∑ rt ∈ Finset.range (c + 1),
        (if (rx + m + rt ≤ c ∧ rx + m + rt ≤ h) then
          qpow (-(chooseTwo rx : ℤ) - (chooseTwo m : ℤ) - (chooseTwo rt : ℤ) - (rx : ℤ) * (m : ℤ) -
            ((rx : ℤ) + (m : ℤ)) * (rt : ℤ)) *
            (A rx (h - (rx + m + rt)) * (PowerSeries.coeff m D * Cq (c - (rx + m + rt)) rt))
        else 0) := by sorry
