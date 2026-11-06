-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_tracePrefixField_normalized
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.tracePrefixField_normalized
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:17:11.932525+00:00
-- url     : https://prove2.me/theorems/95772f62-0b8e-4128-b47d-cb58b38d47f6
-- title:
--   F256 Garcia Stichtenoth: trace Prefix Field normalized
-- statement:
--   Every prefix of the actual trace-coordinate chain is a normalized
--   refinement, and its terminal coordinate is normalized at the fixed prime.
--   Only the starting parameter carries an order hypothesis.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/TraceRefinement.lean#L88-L116
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/TraceRefinement.lean#L88-L116

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_NormalizedCompositumEdges
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_TraceRefinement
set_option autoImplicit false
open IntermediateField
open scoped QEC.Coding.AlgebraicGeometry.IntermediateIntegralModels
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
variable {F E : Type*} [_root_.Field F] [_root_.Field E] [Algebra F E]
variable (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra A F] [IsFractionRing A F] [Algebra A E] [IsScalarTower A F E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E]
    [Algebra F256 F] [Algebra F256 E] [IsScalarTower F256 F E]
    [Module.Finite A (integralClosure A E)]
    (Q : IsDedekindDomain.HeightOneSpectrum (integralClosure A E))
local notation "P" => IntermediateIntegralModels.prime A F E Q

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.tracePrefixField_normalized
    (K : IntermediateField F E) (t : ℕ → E) (ht : t 0 ∈ K) (n : ℕ)
    (heq : ∀ j < n, t (j + 1) ^ 2 + t (j + 1) = t j)
    (hzero : (heightOnePlace (k := F256) (K := K) (P K)).order ⟨t 0, ht⟩ = -1 ∨
      0 ≤ (heightOnePlace (k := F256) (K := K) (P K)).order ⟨t 0, ht⟩) :
    NormalizedRefinement A F E Q K (tracePrefixField K t n) ∧
      ((heightOnePlace (k := F256) (K := tracePrefixField K t n)
        (P (tracePrefixField K t n))).order
          ⟨t n, tracePrefixField_coordinate_mem K t ht n⟩ = -1 ∨
        0 ≤ (heightOnePlace (k := F256) (K := tracePrefixField K t n)
          (P (tracePrefixField K t n))).order
            ⟨t n, tracePrefixField_coordinate_mem K t ht n⟩) := by sorry
