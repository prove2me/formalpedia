-- Prove2me | Theorems.Thm_TypeDensity_squarefree_map_of_isSeparable
-- name    : TypeDensity.squarefree_map_of_isSeparable
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:00:38.546042+00:00
-- url     : https://prove2.me/theorems/4cfe61a6-7156-47b5-b8c2-b67bc5bd101b
-- title:
--   Along a finite separable extension `K'/K`, the image of an irreducible polynomial stays squarefree (`K' ⊗_K K[X]/(g)` is formally unramified over the field `K[X]/(g)`, hence reduced).
-- statement:
--   Along a finite separable extension `K'/K`, the image of an irreducible polynomial stays squarefree (`K' ⊗_K K[X]/(g)` is formally unramified over the field `K[X]/(g)`, hence reduced).
-- source:
--   TypeDensity/Algebra/AlgebraType.lean#L244-L255

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Theorems.Thm_TypeDensity_adjoinRoot_tensor
import Theorems.Thm_TypeDensity_squarefree_of_isReduced_adjoinRoot
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

theorem TypeDensity.squarefree_map_of_isSeparable [FiniteDimensional K K'] [Algebra.IsSeparable K K']
    (g : K[X]) [Fact (Irreducible g)] : Squarefree (g.map (algebraMap K K')) := by sorry
