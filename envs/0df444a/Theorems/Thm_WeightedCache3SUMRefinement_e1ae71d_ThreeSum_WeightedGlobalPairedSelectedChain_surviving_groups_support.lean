-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalPairedSelectedChain_surviving_groups_support
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPairedSelectedChain.surviving_groups_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T11:34:42.05328+00:00
-- url     : https://prove2.me/theorems/811c4efe-b693-4133-8900-67fba34d6db9
-- title:
--   surviving_groups_support
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryPairedSelectedChain.lean#L141-L175
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryPairedSelectedChain.lean#L141-L175

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPairedCarryBudget
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPairedCollisionRate
import Definitions.Def_Submission_ThreeSum_LightTernaryRowSelector
import Definitions.Def_Submission_ThreeSum_TernaryPairedSupportConcrete
import Definitions.Def_Submission_ThreeSum_TernaryOriginalCollisions
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPairedSelectedChain
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPairedSelectedChain
open Filter Real Finset TernaryPairedRecurrence TernaryPairedInitial WeightedGlobalPairedNativeDrift
open WeightedGlobalOversizePrime WeightedGlobalOversizeOverhead WeightedGlobalCoverScale WeightedGlobalLocalParameters TernaryCoverLocal
open WeightedGlobalEntropyRates
open WeightedGlobalSignedPadding TernaryPairedPotential TernaryPairedSupportConcrete
open scoped Topology BigOperators
set_option maxHeartbeats 1000000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPairedSelectedChain.surviving_groups_support {F W B C G D : Type*}
    [Field F] [Fintype F] [AddCommGroup W] [Module F W] [Fintype W]
    [Fintype B] [Fintype C] [Fintype G] [DecidableEq B] [DecidableEq C]
    [DecidableEq W] [DecidableEq D]
    (J K total : ℕ) (L : B→Fin J→ℤ) (R : C→Fin J→ℤ)
    (H : (Fin J→F)→ₗ[F] W)
    (P : G→Type*) [∀ g, Fintype (P g)]
    (left : ∀ g, P g→{b : B // b∉TernaryOriginalCollisions.deleted (fun b => H (fun j => (L b j : F)))})
    (right : ∀ g, P g→{c : C // c∉TernaryOriginalCollisions.deleted (fun c => H (fun j => (R c j : F)))})
    (root : G→W) (mode : ∀ g, P g→D)
    (hroot : ∀ g a, H ((fun j => (L (left g a).val j : F))+(fun j => (R (right g a).val j : F)))=root g)
    (hraw : ∀ g a b, (fun j => (L (left g a).val j : F))+(fun j => (R (right g a).val j : F))=
      (fun j => (L (left g b).val j : F))+(fun j => (R (right g b).val j : F))→mode g a=mode g b)
    (hsource : ∀ g a b, left g a=left g b → right g a=right g b → mode g a=mode g b)
    (hpotential : (∑ g : G, ∑ e : Fin K→P g,
      rowWeight (tupleMatrix (fun a => L (left g a).val) (fun a => R (right g a).val) e))≤total)
    (hzero : total=0) :
    ∀ g, (TernaryPairedSupport.physicalSupport (mode g)).card≤2*Fintype.card F^K := by sorry
