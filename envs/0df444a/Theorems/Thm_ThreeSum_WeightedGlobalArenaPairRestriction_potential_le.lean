-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaPairRestriction_potential_le
-- name    : ThreeSum.WeightedGlobalArenaPairRestriction.potential_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:57:28.950214+00:00
-- url     : https://prove2.me/theorems/534ac92e-7e73-45d0-89e6-e2b52a54a981
-- title:
--   Weighted Global Arena Pair Restriction: potential le
-- statement:
--   Physical singleton compaction only removes nonnegative original tuple
--   summands. Dictionary multiplicities and every wanted occurrence remain exact.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPairRestriction.lean#L80-L104
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPairRestriction.lean#L80-L104

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceSetup
import Definitions.Def_Submission_Weighted_Global_TernaryNativeTensorScore
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPairRestriction
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaPairRestriction
open Finset TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps WeightedGlobalArenaSourceSetup
open WeightedGlobalNativePairMoments WeightedGlobalNativeTensorScore
open scoped BigOperators
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 3000000
variable {p m F r : ℕ} [Fact p.Prime]
variable (maps : Fin F→Weight m p) (τ cap : ℕ) (Q : WeightedGlobalGoodOutputCatalog.Output m)
    (I : Input) (nB nC : ℕ) (fB fC : ℕ→ℕ)
    (hB : ∀ i<nB, fB i<I.nB) (hC : ∀ i<nC, fC i<I.nC)
include hB hC

theorem ThreeSum.WeightedGlobalArenaPairRestriction.potential_le (K J : ℕ) (L R : ℕ→ℕ→ℤ)
    (hfB : ∀ a<nB, ∀ b<nB, fB a=fB b→a=b)
    (hfC : ∀ a<nC, ∀ b<nC, fC a=fC b→a=b) :
    pairedPotential (small (r := r) maps τ cap Q I nB nC fB fC) K J
      (fun i => L (fB i)) (fun i => R (fC i))≤
      pairedPotential (full (r := r) maps τ cap Q I) K J L R := by sorry
