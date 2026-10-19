-- Prove2me | Theorems.Thm_TypeDensity_qcongr_crossingQ_mul_qdagger
-- name    : TypeDensity.qcongr_crossingQ_mul_qdagger
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T15:38:58.225225+00:00
-- url     : https://prove2.me/theorems/38161fb7-d827-48de-a5e0-064c7672e539
-- title:
--   If `G_b ≡ S(B_bᵛ)` through degree `M` for all `b > 0`, then `U_{a,b}` is unitary, `U_{a,b} U_{a,b}† ≡ 1`, through total contact degree `2M + 1`.
-- statement:
--   If `G_b ≡ S(B_bᵛ)` through degree `M` for all `b > 0`, then `U_{a,b}` is unitary, `U_{a,b} U_{a,b}† ≡ 1`, through total contact degree `2M + 1`.
-- source:
--   TypeDensity/Reciprocity/Patterns.lean#L852-L898

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Formula_StateCombinatorics
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
import Definitions.Def_TypeDensity_Reciprocity_Patterns
import Theorems.Thm_TypeDensity_qpow_zero
import Theorems.Thm_TypeDensity_QCongr_mono
import Theorems.Thm_TypeDensity_QCongr_trans
import Theorems.Thm_TypeDensity_QCongr_qmul
import Theorems.Thm_TypeDensity_qplus_qmul
import Theorems.Thm_TypeDensity_qminus_qmul
import Theorems.Thm_TypeDensity_qone_qmul
import Theorems.Thm_TypeDensity_qcongr_qplus_qone
import Theorems.Thm_TypeDensity_qcongr_qminus_qone
import Theorems.Thm_TypeDensity_crossingQ_zero_zero
import Theorems.Thm_TypeDensity_crossingQ_eq_qmul_qplus_qdiag_qminus
import Theorems.Thm_TypeDensity_dilate_recipSer_eulerSer_mul_scongr_one
import Theorems.Thm_TypeDensity_QPositive_qmul
import Theorems.Thm_TypeDensity_QPositive_qdagger
import Theorems.Thm_TypeDensity_qmul_zero_zero
import Theorems.Thm_TypeDensity_qdagger_qmul
import Theorems.Thm_TypeDensity_qdagger_qplus
import Theorems.Thm_TypeDensity_qdagger_qminus
import Theorems.Thm_TypeDensity_qmul_assoc
import Theorems.Thm_TypeDensity_qcongr_qdiag_mul_qdagger
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

theorem TypeDensity.qcongr_crossingQ_mul_qdagger (M : ℕ) (hS : ∀ a : ℕ, 0 < a →
    SCongr M (eulerSer 0 a) (dilate (recipSer (clusterSer a)))) (j : ℕ) (hj : j ≤ 2 * M + 1)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    QCongr j (qmul (crossingQ a b) (qdagger (crossingQ a b))) qone := by sorry
