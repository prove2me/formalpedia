-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaSelectedTerminal_native_zero
-- name    : ThreeSum.WeightedGlobalArenaSelectedTerminal.native_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T22:46:49.729538+00:00
-- url     : https://prove2.me/theorems/94633ef7-b1bf-4803-9209-3ae2e381f25a
-- title:
--   Weighted Global Arena Selected Terminal: native zero
-- statement:
--   The Weighted Global Arena Selected Terminal construction uses the native zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSelectedTerminal.lean#L32-L43
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSelectedTerminal.lean#L32-L43

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSelectedBudgets
import Definitions.Def_Submission_Weighted_Global_TernaryArenaCompactSupport
import Definitions.Def_Submission_Weighted_Global_TernaryPairedBudgetCollision
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSelectedTerminal
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaSelectedTerminal
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalArenaSeedData
open WeightedGlobalArenaBudgetExistence WeightedGlobalArenaSelectedBudgets
set_option maxHeartbeats 5000000
variable {p m F : ℕ} [Fact p.Prime]
variable (maps : Fin F→Weight m p) (τ cap : ℕ) (Q : WeightedGlobalGoodOutputCatalog.Output m)
    (I : Input) (A : Inputs) (K n U0 : ℕ) (L R O : ℕ→ℕ→ℤ) (r : ℕ) (s : State (p := p) A)

theorem ThreeSum.WeightedGlobalArenaSelectedTerminal.native_zero (M C : ℕ)
    (hbudget : Budget maps τ cap Q I A K n U0 L R O r s)
    (hb : 0<9*pairFactor m F K)
    (hdrift : (9*pairFactor m F K)^4*M^(4*K+3)≤(p^(2*K))^4)
    (hcover : n^2≤M^r) (hinit : U0^4≤C*n^(8*K+5)) (hn : C<n) :
    WeightedGlobalNativeTensorScore.pairedPotential
      (setup (r := r) maps τ cap Q (input I A s L R O r)) K A.J L R=0 := by sorry
