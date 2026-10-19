-- Prove2me | Theorems.Thm_TypeDensity_adamsSer_clusterSer_sub_one_scongr
-- name    : TypeDensity.adamsSer_clusterSer_sub_one_scongr
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:01:54.343057+00:00
-- url     : https://prove2.me/theorems/8ae2e178-75bc-4b2d-a6d1-da95a431525a
-- title:
--   Through degree `n`, `ψ_m(B_a) - 1` is the finite sum `Σ_{r < n} ψ_m(F_{S(a;r+1)}) x^{m(r+1)}`.
-- statement:
--   Through degree `n`, `ψ_m(B_a) - 1` is the finite sum `Σ_{r < n} ψ_m(F_{S(a;r+1)}) x^{m(r+1)}`.
-- source:
--   TypeDensity/Reciprocity/Defs.lean#L365-L391

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Theorems.Thm_TypeDensity_coeff_adamsSer
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

theorem TypeDensity.adamsSer_clusterSer_sub_one_scongr (a m n : ℕ) (hm : 0 < m) :
    SCongr n (adamsSer m (clusterSer a) - 1)
      (∑ r : Fin n, PowerSeries.C (adamsCoef m (lawCoef (stateLaw (State.single a (r.val + 1))))) *
        (PowerSeries.X : Ser) ^ (m * (r.val + 1))) := by sorry
