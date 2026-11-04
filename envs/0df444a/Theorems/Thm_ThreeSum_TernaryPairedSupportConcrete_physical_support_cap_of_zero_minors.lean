-- Prove2me | Theorems.Thm_ThreeSum_TernaryPairedSupportConcrete_physical_support_cap_of_zero_minors
-- name    : ThreeSum.TernaryPairedSupportConcrete.physical_support_cap_of_zero_minors
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:27:38.352687+00:00
-- url     : https://prove2.me/theorems/84f4b986-e967-4aff-989b-8b2b2ae964c1
-- title:
--   Ternary Paired Support Concrete: physical support cap of zero minors
-- statement:
--   The Ternary Paired Support Concrete construction uses the physical support cap of zero minors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedSupportConcrete.lean#L67-L85
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedSupportConcrete.lean#L67-L85

import Definitions.Def_Submission_ThreeSum_TernaryPairedPotential
import Definitions.Def_Submission_ThreeSum_TernaryPairedSupportConcrete
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPairedSupportConcrete
open Finset TernaryPairedPotential TernaryPairedSupport
open scoped BigOperators
variable {K : Type*} [Field K]
variable {P W D : Type*} [Fintype P] [Fintype K]
  [AddCommGroup W] [Module K W] [Fintype W] [DecidableEq D]

theorem ThreeSum.TernaryPairedSupportConcrete.physical_support_cap_of_zero_minors {J : ℕ}
    (L R : P → Fin J → ℤ) (H : (Fin J → K) →ₗ[K] W) (o : W)
    (mode : P → D) (m : ℕ)
    (hroot : ∀ a, H ((fun j => (L a j : K))+(fun j => (R a j : K)))=o)
    (hmode : ∀ a b, (fun j => (L a j : K))+(fun j => (R a j : K)) =
      (fun j => (L b j : K))+(fun j => (R b j : K)) → mode a=mode b)
    (hhash : ∀ a b, H (fun j => (L a j : K))=H (fun j => (L b j : K)) → mode a=mode b)
    (hzero : (∑ e : Fin m → P, rowWeight (tupleMatrix L R e))=0) :
    (physicalSupport mode).card ≤ 2*Fintype.card K^m := by sorry
