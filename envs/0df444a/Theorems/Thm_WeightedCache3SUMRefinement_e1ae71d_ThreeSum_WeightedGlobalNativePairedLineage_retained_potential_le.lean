-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalNativePairedLineage_retained_potential_le
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalNativePairedLineage.retained_potential_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T12:23:53.87533+00:00
-- url     : https://prove2.me/theorems/0ded9503-0d02-4ade-b58e-de89ae0552c6
-- title:
--   retained_potential_le
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryNativePairedLineage.lean#L24-L50
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryNativePairedLineage.lean#L24-L50

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_TernaryPairedContraction
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryNativePairMoments
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryRepeatedWords
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryGoodOutputCatalog
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryNativePairedLineage
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalNativePairedLineage
open Finset TernaryJointType TernaryCoverLocal TernaryCoverOutputCap
open TernaryOriginalRowMenu TernaryPairedPotential TernaryPairedContraction
open scoped BigOperators
set_option maxHeartbeats 3000000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalNativePairedLineage.retained_potential_le {p : ℕ} [Fact p.Prime]
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
