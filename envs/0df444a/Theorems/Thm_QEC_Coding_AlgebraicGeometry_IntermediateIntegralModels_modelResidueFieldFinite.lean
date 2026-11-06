-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_IntermediateIntegralModels_modelResidueFieldFinite
-- name    : QEC.Coding.AlgebraicGeometry.IntermediateIntegralModels.modelResidueFieldFinite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:52:06.263452+00:00
-- url     : https://prove2.me/theorems/5f0e3336-c3c0-4177-9594-b0a864dabb5f
-- title:
--   Intermediate Integral Models: model Residue Field Finite
-- statement:
--   Finiteness of the residue field at every intermediate prime follows
--   from finiteness over the initial DVR, without rebuilding function-field
--   presentations for each compositum.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/IntermediateIntegralModels.lean#L168-L191
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/IntermediateIntegralModels.lean#L168-L191

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_HeightOneOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_HeightOneQuotientResidue
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.FieldTheory.IntermediateField.Algebraic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_IntermediateIntegralModels
set_option autoImplicit false
open IntermediateField
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.IntermediateIntegralModels
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
variable (A F E : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field F] [Field E] [Algebra A F] [IsFractionRing A F]
    [Algebra F E] [Algebra A E] [IsScalarTower A F E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E]
local notation "C" => Model A F E
variable [IsDedekindDomain (integralClosure A E)] [Module.Finite A (integralClosure A E)]
omit [IsDedekindDomain (integralClosure A E)] [Module.Finite A (integralClosure A E)]

theorem QEC.Coding.AlgebraicGeometry.IntermediateIntegralModels.modelResidueFieldFinite
    {k : Type*} [Field k] [Finite k]
    [Algebra k F] [Algebra k E] [IsScalarTower k F E]
    [Finite (IsLocalRing.ResidueField A)]
    (K : IntermediateField F E) (H : IsDedekindDomain.HeightOneSpectrum (C K)) :
    Finite (heightOnePlace (k := k) (K := K) H).residueField := by sorry
