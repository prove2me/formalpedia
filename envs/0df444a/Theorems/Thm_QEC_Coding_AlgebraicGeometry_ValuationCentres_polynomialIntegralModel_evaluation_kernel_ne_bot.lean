-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_ValuationCentres_polynomialIntegralModel_evaluation_kernel_ne_bot
-- name    : QEC.Coding.AlgebraicGeometry.ValuationCentres.polynomialIntegralModel_evaluation_kernel_ne_bot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:09:53.015439+00:00
-- url     : https://prove2.me/theorems/c96e9c67-4d0f-43b1-98c7-833621096d8f
-- title:
--   Valuation Centres: polynomial Integral Model evaluation kernel ne bot
-- statement:
--   Evaluating an integral model containing a genuine polynomial coordinate
--   over its scalar field has a nonzero kernel: the coordinate minus its evaluated constant.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/ValuationCentres.lean#L21-L44
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/ValuationCentres.lean#L21-L44

import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.AlgebraicGeometry.StructureSheaf
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_ValuationCentres
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.ValuationCentres
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.ValuationCentres.polynomialIntegralModel_evaluation_kernel_ne_bot
    {k K : Type*} [Field k] [Field K] [Algebra (Polynomial k) K]
    (hi : Function.Injective (algebraMap (Polynomial k) K))
    (e : integralClosure (Polynomial k) K →+* k)
    (hc : ∀ c : k, e ⟨algebraMap (Polynomial k) K (Polynomial.C c),
      isIntegral_algebraMap⟩ = c) : RingHom.ker e ≠ ⊥ := by sorry
