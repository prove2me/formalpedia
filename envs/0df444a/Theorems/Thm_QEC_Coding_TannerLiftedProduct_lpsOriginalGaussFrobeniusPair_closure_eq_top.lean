-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGaussFrobeniusPair_closure_eq_top
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalGaussFrobeniusPair_closure_eq_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T13:59:43.379036+00:00
-- url     : https://prove2.me/theorems/04087285-1cfd-4391-912e-7019f87ea222
-- title:
--   Tanner Lifted Product: lps Original Gauss Frobenius Pair closure eq top
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Gauss Frobenius Pair closure eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussJointFiber.lean#L56-L74
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussJointFiber.lean#L56-L74

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussFrobeniusFiber
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussJointFiber
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGaussMaximalResidue_charP

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped TensorProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalGaussFrobeniusPair_closure_eq_top
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    letI : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
    letI : CharP (LPSOriginalGaussAffineOrder N hN p ⧸ q) p :=
      lpsOriginalGaussMaximalResidue_charP N hN p q
    Subring.closure (Set.range ((RingHom.id (LPSOriginalGaussAffineOrder N hN p ⧸ q)).prod
      (frobenius (LPSOriginalGaussAffineOrder N hN p ⧸ q) p)) ∪
      Set.range ((frobenius (LPSOriginalGaussAffineOrder N hN p ⧸ q) p).prod
        (RingHom.id (LPSOriginalGaussAffineOrder N hN p ⧸ q)))) = ⊤ := by sorry
