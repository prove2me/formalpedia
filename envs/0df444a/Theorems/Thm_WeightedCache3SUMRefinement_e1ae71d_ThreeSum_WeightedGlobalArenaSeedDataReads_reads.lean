-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaSeedDataReads_reads
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSeedDataReads.reads
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:01:39.380202+00:00
-- url     : https://prove2.me/theorems/f48197e6-968a-4f1d-b6d8-dd6d71f03a29
-- title:
--   reads
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaSeedDataReads.lean#L22-L106
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaSeedDataReads.lean#L22-L106

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSeedPrimitiveGuards
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSeedData
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSeedDataReads
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_row
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_rows
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedCountFrontend_row
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedCountFrontend_rows
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaSourceCountSeed_seed
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaSourceSeed_seed
attribute [local simp] ThreeSum.LightTernaryCountFrontend.row
attribute [local simp] ThreeSum.LightTernaryCountFrontend.rows
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedCountFrontend.row
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedCountFrontend.rows


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSeedDataReads
open Light TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaLayout WeightedGlobalArenaSeedCandidate
open LightWeightedGlobalSeedScoreFactory WeightedGlobalArenaSeedData TernaryExtensionEncoding TernaryOriginalRowMenu
variable {p : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]
set_option maxHeartbeats 6000000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSeedDataReads.reads (I : Input) (A : Inputs) (r b ordinal positionCap : ℕ)
    (ℓ : E→ₗ[ZMod p] ZMod p) (seed : E×E)
    (row : ℕ→(Fin (A.J+2)→ZMod p)→ₗ[ZMod p] ZMod p)
    (L R O : ℕ→Fin (A.J+2)→ℤ) (rows : List (Fin A.J→ZMod p))
    (catalog : ℕ→ℕ→ℕ) (μ : ℕ→ℤ)
    (hBend : A.Bmatrix+I.nB*(A.J+2)≤I.free)
    (hCend : A.Cmatrix+I.nC*(A.J+2)≤I.free)
    (hOend : A.Omatrix+I.requesterCount*(A.J+2)≤I.free)
    (hMenuEnd : A.menu+ordinal*(A.J+2)+(A.J+2)≤I.free)
    (hPositionEnd : A.positions+I.requesterCount≤I.free)
    (hb : b<p)
    (bL : ∀i<I.nB,∀t, |L i t|≤(b : ℤ))
    (bR : ∀i<I.nC,∀t, |R i t|≤(b : ℤ))
    (bO : ∀i<I.requesterCount,∀t, |O i t|≤(b : ℤ))
    (hL : ∀i<I.nB,∀k<A.J+2, μ (A.Bmatrix+i*(A.J+2)+k)=physical L i k)
    (hR : ∀i<I.nC,∀k<A.J+2, μ (A.Cmatrix+i*(A.J+2)+k)=physical R i k)
    (hO : ∀i<I.requesterCount,∀k<A.J+2, μ (A.Omatrix+i*(A.J+2)+k)=physical O i k)
    (hCoeff : ∀(k : ℕ) (hk : k<A.J+2), μ (A.menu+ordinal*(A.J+2)+k)=
      (seedRow (A.J+2) ℓ seed (digitOrder A.J ⟨k,hk⟩)).val)
    (oldB : ∀i<I.nB, μ (addr I.free I.capacity 4+i)=(coefficientCode (hash row r L i) : ℤ))
    (oldC : ∀i<I.nC, μ (addr I.free I.capacity 5+i)=(coefficientCode (hash row r R i) : ℤ))
    (oldO : ∀i<I.requesterCount, μ (addr I.free I.capacity 6+i)=(coefficientCode (hash row r O i) : ℤ))
    (hRep : TernaryStoredSpan.Represents catalog (p^r) (rows.map (TernaryPhysicalDigitSpan.reversal A.J)))
    (hCatalog : ∀k<p^r,∀i<A.J, catalog k i<p)
    (hCatalogRead : ∀k<p^r,∀i<A.J, μ (addr I.free I.capacity 7+A.J*k+i)=(catalog k i : ℤ))
    (hPos : ∀i<I.requesterCount, μ (A.positions+i)=(I.positions i : ℤ))
    (hPosBound : ∀i<I.requesterCount, I.positions i≤positionCap) :
    WeightedGlobalArenaSeedPrimitiveGuards.Reads I A ordinal
      (data I A r b ordinal ℓ seed row L R O rows catalog) μ positionCap := by sorry
