-- Prove2me | Theorems.Thm_TypeDensity_squarefree_of_isReduced_adjoinRoot
-- name    : TypeDensity.squarefree_of_isReduced_adjoinRoot
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:37.536005+00:00
-- url     : https://prove2.me/theorems/580b53d2-2d46-4d39-801a-7f404e730f5a
-- title:
--   A nonzero `q` with `K'[X]/(q)` reduced is squarefree.
-- statement:
--   A nonzero `q` with `K'[X]/(q)` reduced is squarefree.
-- source:
--   TypeDensity/Algebra/AlgebraType.lean#L234-L242

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Algebra_AlgebraType
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
import Mathlib.RingTheory.Henselian
set_option autoImplicit false

open TypeDensity
open scoped TensorProduct
open Polynomial IsLocalRing
variable (K K' : Type) [Field K] [Field K'] [Algebra K K']

theorem TypeDensity.squarefree_of_isReduced_adjoinRoot (q : K'[X]) (hq : q ≠ 0)
    (hred : IsReduced (AdjoinRoot q)) : Squarefree q := by sorry
