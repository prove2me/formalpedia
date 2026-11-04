-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaArgumentWords_args_word
-- name    : ThreeSum.WeightedGlobalArenaArgumentWords.args_word
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T16:50:37.39817+00:00
-- url     : https://prove2.me/theorems/cc918411-b9bb-453a-b29c-1cb798366fe4
-- title:
--   Weighted Global Arena Argument Words: args word
-- statement:
--   The Weighted Global Arena Argument Words construction uses the args word property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaArgumentWords.lean#L34-L110
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaArgumentWords.lean#L34-L110

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaMomentResources
import Definitions.Def_Submission_Weighted_Global_TernaryArenaArgumentWords
import Theorems.Thm_ThreeSum_TernarySourceExecutionFactory_Seed_finish
import Theorems.Thm_ThreeSum_WeightedSourceCountExecutionFactory_Seed_finish

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaArgumentWords
open Light WeightedGlobalArenaSourceSetup WeightedGlobalArenaLayout WeightedGlobalCoverGoodMaps
open WeightedGlobalLocalParameters TernaryJointType
variable {p m F r : ℕ} [Fact p.Prime]
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

theorem ThreeSum.WeightedGlobalArenaArgumentWords.args_word {lim : Limits} {originalB originalC : ℕ}
    (maps : Fin F→Weight m p) (τ cap : ℕ) (Q : WeightedGlobalGoodOutputCatalog.Output m)
    (I : Input) (hw : (lim.space : ℤ)≤lim.word)
    (hend : finish I.free I.capacity≤lim.space)
    (hscalars : scalarControl m p F r (entries (r := r) maps τ I).length≤I.capacity)
    (hnB : I.nB≤I.capacity) (hnC : I.nC≤I.capacity)
    (hprefix : I.prefixFree+4^(N m r)+(2*N m r+1)≤lim.space)
    (hB : originalB+I.nB≤lim.space) (hC : originalC+I.nC≤lim.space) :
    ∀ z∈LightWeightedGlobalMomentChannelFactory.args (setup (r := r) maps τ cap Q I)
      originalB originalC (addr I.free I.capacity 25), |z|≤lim.word := by sorry
