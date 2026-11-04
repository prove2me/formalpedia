-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalNativePairedLineage_retained_potential_le
-- name    : ThreeSum.WeightedGlobalNativePairedLineage.retained_potential_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:03:23.271651+00:00
-- url     : https://prove2.me/theorems/145f0ad3-7d1a-4a0c-810e-21cd1005d309
-- title:
--   Weighted Global Native Paired Lineage: retained potential le
-- statement:
--   Every retained physical child record has one original parent record and
--   one shared map/output/ordered-partition child. Deleting dictionary entries
--   or wanted records only restricts this injection; equal-valued records are
--   kept distinct by their physical occurrence IDs.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryNativePairedLineage.lean#L24-L50
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryNativePairedLineage.lean#L24-L50

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_TernaryPairedContraction
import Definitions.Def_Submission_Weighted_Global_TernaryNativePairMoments
import Definitions.Def_Submission_Weighted_Global_TernaryRepeatedWords
import Definitions.Def_Submission_Weighted_Global_TernaryGoodOutputCatalog
import Definitions.Def_Submission_Weighted_Global_TernaryNativePairedLineage
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalNativePairedLineage
open Finset TernaryJointType TernaryCoverLocal TernaryCoverOutputCap
open TernaryOriginalRowMenu TernaryPairedPotential TernaryPairedContraction
open scoped BigOperators
set_option maxHeartbeats 3000000

theorem ThreeSum.WeightedGlobalNativePairedLineage.retained_potential_le {p : ℕ} [Fact p.Prime]
    {E P Q : Type*} [Field E] [Algebra (ZMod p) E] [Fintype E]
    [DecidableEq E] [Fintype P] [Fintype Q]
    {Λ L K F : ℕ} {α π : DigitType}
    (ℓ : E→ₗ[ZMod p] ZMod p) (A : P→Matrix (Fin (K+K)) (Fin Λ) ℤ)
    (B : Q→Matrix (Fin (K+K)) (Fin Λ) ℤ)
    (maps : Fin F→TernaryCoverHashes.Coordinate (Fin L)→ZMod p)
    (seed : E×E) (lineage : Q→P×Child L K F α π)
    (hinj : Function.Injective lineage)
    (hMatrix : ∀ q, B q=A (lineage q).1)
    (hEvent : ∀ q, seed∈menuEvent ℓ (fun i j => (A (lineage q).1 i j : ZMod p))
      (childTarget maps (lineage q).2)) :
    potential B≤nextPotential (α := α) (π := π) ℓ A maps seed := by sorry
