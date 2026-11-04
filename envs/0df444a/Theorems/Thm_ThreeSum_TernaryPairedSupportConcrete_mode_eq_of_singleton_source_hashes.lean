-- Prove2me | Theorems.Thm_ThreeSum_TernaryPairedSupportConcrete_mode_eq_of_singleton_source_hashes
-- name    : ThreeSum.TernaryPairedSupportConcrete.mode_eq_of_singleton_source_hashes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:27:39.79834+00:00
-- url     : https://prove2.me/theorems/d2d8f7b6-fae8-402d-bc39-e8a2aecf78cd
-- title:
--   Ternary Paired Support Concrete: mode eq of singleton source hashes
-- statement:
--   Singleton buckets on BOTH original source colors imply the required
--   left-hash injection on one fixed wanted root. No injection of local words
--   or uniqueness of an encoded representation is used.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedSupportConcrete.lean#L90-L105
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedSupportConcrete.lean#L90-L105

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

theorem ThreeSum.TernaryPairedSupportConcrete.mode_eq_of_singleton_source_hashes {B C : Type*} {J : ℕ}
    (left : P → B) (right : P → C)
    (L : B → Fin J → K) (R : C → Fin J → K)
    (H : (Fin J → K) →ₗ[K] W) (o : W) (mode : P → D)
    (hleft : Function.Injective (fun b => H (L b)))
    (hright : Function.Injective (fun c => H (R c)))
    (hroot : ∀ a, H (L (left a)+R (right a))=o)
    (hmode : ∀ a b, left a=left b → right a=right b → mode a=mode b) :
    ∀ a b, H (L (left a))=H (L (left b)) → mode a=mode b := by sorry
