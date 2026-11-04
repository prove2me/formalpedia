-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaCleanupAllocation_inputs
-- name    : ThreeSum.WeightedGlobalArenaCleanupAllocation.inputs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T22:27:56.952727+00:00
-- url     : https://prove2.me/theorems/839dc379-fa31-408d-9600-e531dc2bbbe1
-- title:
--   Weighted Global Arena Cleanup Allocation: inputs
-- statement:
--   The Weighted Global Arena Cleanup Allocation construction uses the inputs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaCleanupAllocation.lean#L18-L78
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaCleanupAllocation.lean#L18-L78

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFinalGuardAllocation
import Definitions.Def_Submission_Weighted_Global_TernaryArenaCleanupLayout
import Definitions.Def_Submission_Weighted_Global_TernaryArenaCleanupAllocation
import Theorems.Thm_ThreeSum_LightTernaryBankAssembly_layout
import Theorems.Thm_ThreeSum_LightWeightedBankAssembly_layout
import Theorems.Thm_ThreeSum_WeightedGlobalArenaCleanupLayout_inputs
import Theorems.Thm_ThreeSum_WeightedGlobalArenaFrontBounds_capacity

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaCleanupAllocation
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaPrefixFootprints
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters WeightedGlobalArenaAllocation TernaryExtensionEncoding
set_option maxHeartbeats 8000000
variable {p m F r J : ℕ} [Fact p.Prime]

theorem ThreeSum.WeightedGlobalArenaCleanupAllocation.inputs {lim : Limits} {d M b K H drift scale n U : ℕ}
    (maps : Fin F→Weight m p) (τ cap : ℕ) (Alloc : Allocation maps τ cap M b K H drift scale)
    (I : Input) (aBase nA bBase cBase : ℕ)
    (Row : (TernarySignedReduction.Coordinate J→ZMod p)→ₗ[ZMod p] (Fin r→ZMod p))
    (A B C : ℕ→ℤ) (keysB keysC : ℕ→ℕ) (μ : ℕ→ℤ)
    (hok : (WeightedGlobalArenaAllocationResources.need Alloc n U).Ok lim I.free d)
    (hcap : I.capacity=capacity Alloc.D Alloc.E (n+U)) (hr : r≤Nat.clog M (n^2))
    (hnB : I.nB≤n) (hnC : I.nC≤n) (hn : n<2^(2*N m r))
    (hA : aBase+nA≤I.free) (hB : bBase+I.nB≤I.free) (hC : cBase+I.nC≤I.free)
    (hreadA : ∀i<nA,μ (aBase+i)=A i) (hreadB : ∀i<I.nB,μ (bBase+i)=B i)
    (hreadC : ∀i<I.nC,μ (cBase+i)=C i)
    (hreadKB : ∀i<I.nB,μ (addr I.free I.capacity 4+i)=(keysB i : ℤ))
    (hreadKC : ∀i<I.nC,μ (addr I.free I.capacity 5+i)=(keysC i : ℤ))
    (hkB : ∀i<I.nB,keysB i=coefficientCode (WeightedGlobalNativeRequesterCoverage.sourceLeft Row U b (B i)))
    (hkC : ∀i<I.nC,keysC i=coefficientCode (WeightedGlobalNativeRequesterCoverage.sourceRight Row U b (C i)))
    (habsA : ∀i<nA,|A i|≤(U : ℤ)) (habsB : ∀i<I.nB,|B i|≤(U : ℤ))
    (habsC : ∀i<I.nC,|C i|≤(U : ℤ))
    (hsortedB : ∀i j,i<j→j<I.nB→B i<B j)
    (hsortedC : ∀i j,i<j→j<I.nC→C i<C j) :
    LightWeightedGlobalPreparedPostSelection.Inputs
      (WeightedGlobalArenaCleanupLayout.layout I.free I.capacity aBase nA bBase I.nB cBase I.nC
        (p^r) (2*N m r)) lim d U (2*N m r) μ A B C keysB keysC := by sorry
