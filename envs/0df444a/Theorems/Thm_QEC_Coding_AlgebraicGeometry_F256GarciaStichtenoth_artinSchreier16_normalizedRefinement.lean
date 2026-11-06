-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_artinSchreier16_normalizedRefinement
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.artinSchreier16_normalizedRefinement
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:17:05.609207+00:00
-- url     : https://prove2.me/theorems/b5efe015-8283-411a-836a-d7c82a2e8710
-- title:
--   F256 Garcia Stichtenoth: artin Schreier16 normalized Refinement
-- statement:
--   The source's degree-sixteen additive equation has a normalized
--   four-stage refinement in its literal generated subfield. Neither degree
--   sixteen nor a ramification conclusion is an input.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/TraceRefinement.lean#L121-L140
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/TraceRefinement.lean#L121-L140

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

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.artinSchreier16_normalizedRefinement
    (K : IntermediateField F E) (a : K) (y : E)
    (hy : y ^ 16 + y = (a : E))
    (ha : (heightOnePlace (k := F256) (K := K) (P K)).order a = -1 ∨
      0 ≤ (heightOnePlace (k := F256) (K := K) (P K)).order a) :
    NormalizedRefinement A F E Q K ((K⟮y⟯).restrictScalars F) := by sorry
