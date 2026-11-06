-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_NormalizedEdge_compositum_refinement
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.NormalizedEdge.compositum_refinement
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:14:50.247718+00:00
-- url     : https://prove2.me/theorems/d2b117bc-cce7-4eea-8827-11322ba3b6b2
-- title:
--   Normalized Edge: compositum refinement
-- statement:
--   Sweep a single normalized edge through a finite normalized chain. Each
--   new upper edge is constructed by the preceding two-sided square theorem.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/NormalizedCompositumEdges.lean#L162-L178
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/NormalizedCompositumEdges.lean#L162-L178

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_IntermediateIntegralModels
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticCompositumCell
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differents_RelativeTower
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_NormalizedCompositumEdges
set_option autoImplicit false
open IntermediateField
open scoped QEC.Coding.AlgebraicGeometry.IntermediateIntegralModels
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
variable (A F E : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [_root_.Field F] [_root_.Field E] [Algebra A F] [IsFractionRing A F]
    [Algebra F E] [Algebra A E] [IsScalarTower A F E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E]
    [Algebra F256 F] [Algebra F256 E] [IsScalarTower F256 F E]
    [Module.Finite A (integralClosure A E)]
    (Q : IsDedekindDomain.HeightOneSpectrum (integralClosure A E))
local notation "C" => IntermediateIntegralModels.Model A F E
local notation "P" => IntermediateIntegralModels.prime A F E Q

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.NormalizedEdge.compositum_refinement
    [Finite (IsLocalRing.ResidueField A)]
    {K L M : IntermediateField F E}
    (hLeft : NormalizedEdge A F E Q K L)
    (hRight : NormalizedRefinement A F E Q K M) :
    NormalizedRefinement A F E Q L (L ⊔ M) ∧
      NormalizedEdge A F E Q M (L ⊔ M) := by sorry
