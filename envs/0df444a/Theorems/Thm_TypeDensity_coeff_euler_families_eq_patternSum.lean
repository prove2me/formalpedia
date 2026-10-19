-- Prove2me | Theorems.Thm_TypeDensity_coeff_euler_families_eq_patternSum
-- name    : TypeDensity.coeff_euler_families_eq_patternSum
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:44:30.46315+00:00
-- url     : https://prove2.me/theorems/14b650ce-bf85-4a34-96a6-60acfb45e2aa
-- title:
--   The degree-`n` coefficient of the family expansion of `prod_formalPow_adamsSer_clusterSer_scongr` is the pattern sum `patternSum ε a n n`.
-- statement:
--   The degree-`n` coefficient of the family expansion of `prod_formalPow_adamsSer_clusterSer_scongr` is the pattern sum `patternSum ε a n n`.
-- source:
--   TypeDensity/Reciprocity/Plethysm.lean#L968-L993

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Formula_StateCombinatorics
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
import Theorems.Thm_TypeDensity_rational_divisorCount
import Theorems.Thm_TypeDensity_scalar_mul_eq_smul
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Log
set_option autoImplicit false

open TypeDensity

theorem TypeDensity.coeff_euler_families_eq_patternSum (ε : ℤ) (a n : ℕ) :
    PowerSeries.coeff n (∑ K : Fin n → Fin n → Fin (n + 1),
        PowerSeries.C (scalar (∏ i : Fin n, ((∏ j ∈ Finset.range (∑ r : Fin n, (K i r).val),
        ((availablePoints ε (i.val + 1)).rational - RatFunc.C (j : ℚ))) *
        RatFunc.C ((∏ r : Fin n, ((Nat.factorial (K i r).val : ℕ) : ℚ))⁻¹)))) *
        (PowerSeries.C (∏ i : Fin n, ∏ r : Fin n, (adamsCoef (i.val + 1)
        (lawCoef (stateLaw (State.single a (r.val + 1))))) ^ (K i r).val) *
        (PowerSeries.X : Ser) ^ (∑ i : Fin n, (i.val + 1) * ∑ r : Fin n, (r.val + 1) *
        (K i r).val))) = patternSum ε a n n := by sorry
