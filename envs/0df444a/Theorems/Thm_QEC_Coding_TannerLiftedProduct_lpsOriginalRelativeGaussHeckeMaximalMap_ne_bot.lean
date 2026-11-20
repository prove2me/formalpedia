-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussHeckeMaximalMap_ne_bot
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussHeckeMaximalMap_ne_bot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:29:23.778726+00:00
-- url     : https://prove2.me/theorems/d6b5b7e7-1818-495e-8f7e-8e503f55a19c
-- title:
--   Tanner Lifted Product: lps Original Relative Gauss Hecke Maximal Map ne bot
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Relative Gauss Hecke Maximal Map ne bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussBranches.lean#L466-L479
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussBranches.lean#L466-L479

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussNormalization
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussBranches
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussHeckeMaximalMap_ne_bot
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    q.map (algebraMap (LPSOriginalGaussAffineOrder N hN p)
      (LPSOriginalRelativeGaussHeckeOrder N hN p)) ≠ ⊥ := by sorry
