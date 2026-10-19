-- Prove2me | Theorems.Thm_TypeDensity_gaussPhi_qactRecip_gaussPhiInv
-- name    : TypeDensity.gaussPhi_qactRecip_gaussPhiInv
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:02:30.791426+00:00
-- url     : https://prove2.me/theorems/4e21c965-dc10-4a77-a67d-5b321b629afe
-- title:
--   For symmetric `V`, the Gauss twist conjugates `ρ̄(v V)` to `S⁻¹ ∘ ρ(V†) ∘ S`.
-- statement:
--   For symmetric `V`, the Gauss twist conjugates `ρ̄(v V)` to `S⁻¹ ∘ ρ(V†) ∘ S`.
-- source:
--   TypeDensity/Reciprocity/Quantum.lean#L705-L734

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
import Theorems.Thm_TypeDensity_two_mul_tri
import Theorems.Thm_TypeDensity_qpow_add
import Theorems.Thm_TypeDensity_coeff_dilate
import Theorems.Thm_TypeDensity_coeff_codilate
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

theorem TypeDensity.gaussPhi_qactRecip_gaussPhiInv (V : QSer) (hV : ∀ c h : ℕ, V c h = V h c) (f : Ser) :
    gaussPhi (qactRecip (qrecip V) (gaussPhiInv f)) = codilate (qact (qdagger V) (dilate f)) := by sorry
