-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussHeckeInseparableBranchResidue_purelyInseparable
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussHeckeInseparableBranchResidue_purelyInseparable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:27:26.981924+00:00
-- url     : https://prove2.me/theorems/502d6850-9d63-42fe-bfe5-233d296c7c2f
-- title:
--   Tanner Lifted Product: lps Original Relative Gauss Hecke Inseparable Branch Residue purely Inseparable
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Relative Gauss Hecke Inseparable Branch Residue purely Inseparable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussBranches.lean#L595-L613
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussBranches.lean#L595-L613

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussHeckeInseparableBranchResidue_purelyInseparable
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    letI : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
    letI := lpsOriginalRelativeGaussHeckeInseparableBranchIdeal_maximal N hN p hpN q
    letI := lpsOriginalRelativeGaussHeckeInseparableBranchIdeal_liesOver N hN p hpN q
    letI : Field (LPSOriginalRelativeGaussHeckeOrder N hN p ⧸
        LPSOriginalRelativeGaussHeckeInseparableBranchIdeal N hN p hpN q) := Ideal.Quotient.field _
    IsPurelyInseparable (LPSOriginalGaussAffineOrder N hN p ⧸ q)
      (LPSOriginalRelativeGaussHeckeOrder N hN p ⧸
        LPSOriginalRelativeGaussHeckeInseparableBranchIdeal N hN p hpN q) := by sorry
