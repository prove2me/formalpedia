-- Prove2me | Theorems.Thm_TypeDensity_qcongr_qdiag_mul_qdagger
-- name    : TypeDensity.qcongr_qdiag_mul_qdagger
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:34:11.852139+00:00
-- url     : https://prove2.me/theorems/bd3922a0-5e7f-432f-a641-9889c0dc8e83
-- title:
--   If `S(v P_s) P_s ≡ 1` through degree `M`, then `qdiag(P_s) qdiag(P_s)† ≡ 1` through total degree `2M + 1`.
-- statement:
--   If `S(v P_s) P_s ≡ 1` through degree `M`, then `qdiag(P_s) qdiag(P_s)† ≡ 1` through total degree `2M + 1`.
-- source:
--   TypeDensity/Reciprocity/Quantum.lean#L794-L801

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
import Theorems.Thm_TypeDensity_two_mul_chooseTwo
import Theorems.Thm_TypeDensity_qpow_add
import Theorems.Thm_TypeDensity_qpow_zero
import Theorems.Thm_TypeDensity_recipRat_X
import Theorems.Thm_TypeDensity_SCongr_qdiag
import Theorems.Thm_TypeDensity_recipCoef_scalar
import Theorems.Thm_TypeDensity_coeff_recipSer
import Theorems.Thm_TypeDensity_coeff_dilate
import Theorems.Thm_TypeDensity_qdiag_mul
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

theorem TypeDensity.qcongr_qdiag_mul_qdagger (M s : ℕ)
    (h : SCongr M (dilate (recipSer (eulerSer (-1) s)) * eulerSer (-1) s) 1) :
    QCongr (2 * M + 1) (qmul (qdiag (eulerSer (-1) s)) (qdagger (qdiag (eulerSer (-1) s))))
      qone := by sorry
