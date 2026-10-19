-- Prove2me | Theorems.Thm_TypeDensity_prod_formalPow_adamsSer_clusterSer_scongr
-- name    : TypeDensity.prod_formalPow_adamsSer_clusterSer_scongr
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:20:04.724256+00:00
-- url     : https://prove2.me/theorems/49b23b49-455d-49ea-8479-9ff7cba6e76a
-- title:
--   Truncated product expansion of `Π_{m=1}^n ψ_m(B_a)^{C_m}` as a sum over exponent families `K i r`, obtained by multiplying the expansions of `formalPow_adamsSer_clusterSer_scongr`.
-- statement:
--   This gives the truncated product expansion of `Π_{m=1}^n ψ_m(B_a)^{C_m}` as a sum over exponent families `K i r`, obtained by multiplying the expansions of `formalPow_adamsSer_clusterSer_scongr`.
-- source:
--   TypeDensity/Reciprocity/Plethysm.lean#L394-L421

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Formula_StateCombinatorics
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
import Theorems.Thm_TypeDensity_constantCoeff_adamsSer
import Theorems.Thm_TypeDensity_adamsSer_clusterSer_sub_one_scongr
import Theorems.Thm_TypeDensity_sum_C_mul_X_pow_pow
import Theorems.Thm_TypeDensity_coeff_formalPow
import Theorems.Thm_TypeDensity_scalar_eq_algebraMap
import Theorems.Thm_TypeDensity_rat_smul_eq_scalar_mul
import Theorems.Thm_TypeDensity_SCongr_of_eq
import Theorems.Thm_TypeDensity_SCongr_trans
import Theorems.Thm_TypeDensity_SCongr_mul
import Theorems.Thm_TypeDensity_SCongr_pow
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

theorem TypeDensity.prod_formalPow_adamsSer_clusterSer_scongr (ε : ℤ) (a n : ℕ) :
    SCongr n (∏ m ∈ Finset.Icc 1 n, formalPow (availablePoints ε m).rational
        (adamsSer m (clusterSer a))) (∑ K : Fin n → Fin n → Fin (n + 1),
        PowerSeries.C (scalar (∏ i : Fin n, ((∏ j ∈ Finset.range (∑ r : Fin n, (K i r).val),
        ((availablePoints ε (i.val + 1)).rational - RatFunc.C (j : ℚ))) *
        RatFunc.C ((∏ r : Fin n, ((Nat.factorial (K i r).val : ℕ) : ℚ))⁻¹)))) *
        (PowerSeries.C (∏ i : Fin n, ∏ r : Fin n, (adamsCoef (i.val + 1)
        (lawCoef (stateLaw (State.single a (r.val + 1))))) ^ (K i r).val) *
        (PowerSeries.X : Ser) ^ (∑ i : Fin n, (i.val + 1) * ∑ r : Fin n, (r.val + 1) *
        (K i r).val))) := by sorry
