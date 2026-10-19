-- Prove2me | Theorems.Thm_TypeDensity_coeff_pPow_sub_of_scongr
-- name    : TypeDensity.coeff_pPow_sub_of_scongr
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:32:53.291596+00:00
-- url     : https://prove2.me/theorems/88aa87bb-ffcd-429c-a990-03205089d002
-- title:
--   If `g ≡ h` below degree `n`, then the degree-`n` coefficients of `P_w(g)` and `P_w(h)` differ by `w` times those of `g` and `h`.
-- statement:
--   If `g ≡ h` below degree `n`, then the degree-`n` coefficients of `P_w(g)` and `P_w(h)` differ by `w` times those of `g` and `h`.
-- source:
--   TypeDensity/Reciprocity/Plethysm.lean#L465-L478

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Formula_StateCombinatorics
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
import Theorems.Thm_TypeDensity_coeff_expSer_sub_of_scongr
import Theorems.Thm_TypeDensity_coeff_logSer_sub_of_scongr
import Theorems.Thm_TypeDensity_SCongr_plethSum
import Theorems.Thm_TypeDensity_SCongr_moebiusSum
import Theorems.Thm_TypeDensity_adamsCoef_one
import Theorems.Thm_TypeDensity_constantCoeff_plethSum
import Theorems.Thm_TypeDensity_SCongr_C_mul
import Theorems.Thm_TypeDensity_SCongr_logSer
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

theorem TypeDensity.coeff_pPow_sub_of_scongr (n : ℕ) (hn : 0 < n) (w : RatFunc ℚ) (g h : Ser)
    (hg : PowerSeries.constantCoeff g = 1) (hh : PowerSeries.constantCoeff h = 1)
    (hgh : SCongr (n - 1) g h) :
    PowerSeries.coeff n (pPow w g) - PowerSeries.coeff n (pPow w h) =
      scalar w * (PowerSeries.coeff n g - PowerSeries.coeff n h) := by sorry
