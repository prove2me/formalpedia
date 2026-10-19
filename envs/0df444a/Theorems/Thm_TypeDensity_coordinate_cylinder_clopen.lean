-- Prove2me | Theorems.Thm_TypeDensity_coordinate_cylinder_clopen
-- name    : TypeDensity.coordinate_cylinder_clopen
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:04.811982+00:00
-- url     : https://prove2.me/theorems/a36752bd-d6bb-4fa9-85a0-aab0398baca2
-- title:
--   For an `I`-adic topology, the congruence cylinders `{b | ∀ j, b j - a j ∈ I ^ L}` are clopen (hence compact when `O` is compact), and their products are closed.
-- statement:
--   For an `I`-adic topology, the congruence cylinders `{b | ∀ j, b j - a j ∈ I ^ L}` are clopen (hence compact when `O` is compact), and their products are closed.
-- source:
--   TypeDensity/Formula/LawAlgebra.lean#L729-L754

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
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
set_option autoImplicit false

open TypeDensity
open scoped BigOperators ENNReal

theorem TypeDensity.coordinate_cylinder_clopen (O : Type) [CommRing O] [TopologicalSpace O]
    [IsTopologicalRing O] (I : Ideal O) (htop : IsAdic I) (L : ℕ) :
    (∀ (n : ℕ) (a : Fin n → O), IsOpen {b : Fin n → O | ∀ j, b j - a j ∈ I ^ L} ∧
        IsClosed {b : Fin n → O | ∀ j, b j - a j ∈ I ^ L}) ∧
      (∀ (n : ℕ) (a : Fin n → O), CompactSpace O →
        IsCompact {b : Fin n → O | ∀ j, b j - a j ∈ I ^ L}) ∧
      (∀ (ι : Type) (d : ι → ℕ) (c : ∀ i, Fin (d i) → O),
        IsClosed (Set.pi Set.univ fun i ↦ {b : Fin (d i) → O | ∀ j, b j - c i j ∈ I ^ L})) := by sorry
