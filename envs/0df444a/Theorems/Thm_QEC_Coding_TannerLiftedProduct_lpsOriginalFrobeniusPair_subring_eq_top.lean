-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFrobeniusPair_subring_eq_top
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFrobeniusPair_subring_eq_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T11:51:57.662917+00:00
-- url     : https://prove2.me/theorems/eb96c46b-9159-4228-9f61-7eb15e786f0d
-- title:
--   Tanner Lifted Product: lps Original Frobenius Pair subring eq top
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Frobenius Pair subring eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussJointFiber.lean#L27-L54
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussJointFiber.lean#L27-L54

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussFrobeniusFiber
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussJointFiber
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped TensorProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFrobeniusPair_subring_eq_top
    {K : Type*} [Field K] (p : ℕ) (S : Subring (K × K))
    (hfirst : ∀ a : K, (a, a^p) ∈ S)
    (hsecond : ∀ a : K, (a^p, a) ∈ S)
    (u : K) (hu : (u^p)^p ≠ u) : S = ⊤ := by sorry
