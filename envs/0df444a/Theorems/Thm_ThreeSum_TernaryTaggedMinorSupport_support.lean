-- Prove2me | Theorems.Thm_ThreeSum_TernaryTaggedMinorSupport_support
-- name    : ThreeSum.TernaryTaggedMinorSupport.support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:23:23.226195+00:00
-- url     : https://prove2.me/theorems/64f70667-2170-4131-a704-3db90ec5ee81
-- title:
--   Ternary Tagged Minor Support: support
-- statement:
--   The Ternary Tagged Minor Support construction uses the support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryTaggedMinorSupport.lean#L19-L52
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryTaggedMinorSupport.lean#L19-L52

import Definitions.Def_Submission_ThreeSum_TernaryPairedSupportConcrete
import Definitions.Def_Submission_ThreeSum_TernaryTaggedMinorSupport
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryTaggedMinorSupport
open TernaryPairedSupport TernaryPairedPotential
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {p Λ : ℕ} [Fact p.Prime]
variable {P W D : Type*} [Fintype P] [AddCommGroup W] [Module (ZMod p) W] [Fintype W] [DecidableEq D]

theorem ThreeSum.TernaryTaggedMinorSupport.support (L R : P→Fin Λ→ℤ) (a b : Fin Λ)
    (hL : ∀ x, L x a=1 ∧ L x b=0) (hR : ∀ x, R x a=0 ∧ R x b=1)
    (H : (Fin Λ→ZMod p)→ₗ[ZMod p] W) (o : W) (mode : P→D) (K : ℕ)
    (hroot : ∀ x, H ((fun j => (L x j : ZMod p))+(fun j => (R x j : ZMod p)))=o)
    (hmode : ∀ x y, (fun j => (L x j : ZMod p))+(fun j => (R x j : ZMod p))=
      (fun j => (L y j : ZMod p))+(fun j => (R y j : ZMod p))→mode x=mode y)
    (hhash : ∀ x y, H (fun j => (L x j : ZMod p))=H (fun j => (L y j : ZMod p))→mode x=mode y)
    (hzero : (∑ e : Fin K→P, rowWeight (Sum.elim (fun k => L (e k)) (fun k => R (e k))))=0) :
    (physicalSupport mode).card≤2*p^K := by sorry
