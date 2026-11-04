-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaFinalGuardAllocation_guards
-- name    : ThreeSum.WeightedGlobalArenaFinalGuardAllocation.guards
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T22:24:05.436851+00:00
-- url     : https://prove2.me/theorems/647be361-ea75-49e0-9040-eb6e8ef899b5
-- title:
--   Weighted Global Arena Final Guard Allocation: guards
-- statement:
--   All final scalar guards come from the actual fixed arena allocation.
--   Only the literal family cover and a charged query-time upper bound remain
--   as mathematical parameters; there is no execution or source-model oracle.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaFinalGuardAllocation.lean#L30-L119
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaFinalGuardAllocation.lean#L30-L119

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFinalBounds
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPostCertificate
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceArithmetic
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFinalGuardAllocation
import Theorems.Thm_ThreeSum_WeightedGlobalArenaFrontBounds_capacity

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaFinalGuardAllocation
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaPrefixFootprints
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters WeightedGlobalArenaAllocation
set_option maxHeartbeats 10000000
set_option maxRecDepth 24000
variable {p m F r : ℕ} [Fact p.Prime]

theorem ThreeSum.WeightedGlobalArenaFinalGuardAllocation.guards {lim : Limits} {d M b K H drift scale n U nB nC : ℕ}
    (maps : Fin F→Weight m p) (τ cap : ℕ) (Q : WeightedGlobalGoodOutputCatalog.Output m)
    (Alloc : Allocation maps τ cap M b K H drift scale) (I : Input)
    (hok : (WeightedGlobalArenaAllocationResources.need Alloc n U).Ok lim I.free d)
    (hcap : I.capacity=capacity Alloc.D Alloc.E (n+U))
    (hr : r≤Nat.clog M (n^2)) (hM : 1<M) (hF : 1<F) (hN : 0<N m r)
    (hnB : nB≤n) (hnC : nC≤n) (hIB : I.nB≤nB) (hIC : I.nC≤nC)
    (hO : I.requesterCount≤n*2^(LightWeightedGlobalDimensions.J M b n U))
    (hweight : I.weightCap=weight H (4^fixedLength m) U)
    (hprefix : I.prefixFree=addr I.free I.capacity 13)
    (hcover : ∀a b : ZMod p, ∃i, WeightedGlobalCoverFrequency.Covers m p cap τ (maps i) (a,b))
    (htime : WeightedGlobalArenaCountReady.queryTime (m := m) (r := r) I
      (valueCap (r := r) maps cap I)≤I.queryTime) :
    WeightedGlobalArenaPostCertificate.Guards (r := r) maps τ cap Q I lim d M n U H nB nC := by sorry
