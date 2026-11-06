-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_normalizedLiteralRoot_order
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.normalizedLiteralRoot_order
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:14:05.21594+00:00
-- url     : https://prove2.me/theorems/ef55b287-c8d7-46f1-9d5d-a0d757904ddb
-- title:
--   F256 Garcia Stichtenoth: normalized Literal Root order
-- statement:
--   A literal normalized quadratic equation propagates normalized order to
--   its actual root, including degree-one stages of an embedded refinement.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/NormalizedCompositumEdges.lean#L51-L64
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/NormalizedCompositumEdges.lean#L51-L64

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

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.normalizedLiteralRoot_order
    {K L : IntermediateField F E} [Fact (K ≤ L)]
    (a : K) (y : L) (hy : y ^ 2 + y = algebraMap K L a)
    (hgen : K⟮y⟯ = ⊤)
    (ha : (heightOnePlace (k := F256) (K := K) (P K)).order a = -1 ∨
      0 ≤ (heightOnePlace (k := F256) (K := K) (P K)).order a) :
    (heightOnePlace (k := F256) (K := L) (P L)).order y = -1 ∨
      0 ≤ (heightOnePlace (k := F256) (K := L) (P L)).order y := by sorry
