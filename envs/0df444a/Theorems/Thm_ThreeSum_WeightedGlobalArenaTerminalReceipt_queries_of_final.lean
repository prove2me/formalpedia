-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaTerminalReceipt_queries_of_final
-- name    : ThreeSum.WeightedGlobalArenaTerminalReceipt.queries_of_final
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T02:07:16.571722+00:00
-- url     : https://prove2.me/theorems/0f3908e3-ea5a-4013-aac3-54e3abf353e4
-- title:
--   Weighted Global Arena Terminal Receipt: queries of final
-- statement:
--   Plan.Final's retained replay reads suffice for all actual metadata and
--   106 host words; the execution proof itself need not be retained in memory.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaTerminalReceipt.lean#L84-L146
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaTerminalReceipt.lean#L84-L146

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPhaseBudget
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFinalMetadata
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFinalSolver
import Definitions.Def_Submission_Weighted_Global_TernaryArenaLoopState
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPreparedMemory
import Definitions.Def_Submission_Weighted_Global_TernaryArenaTerminalReceipt
import Theorems.Thm_ThreeSum_WeightedGlobalArenaFrontBounds_capacity

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaTerminalReceipt
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
open WeightedGlobalArenaSeedData WeightedGlobalArenaSelectedBudgets WeightedGlobalArenaBudgetExistence WeightedGlobalArenaFamilyBudget
open WeightedGlobalArenaSelectedSigned WeightedGlobalArenaSelectedTerminal WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters
open LightWeightedGlobalSeedScoreFactory LightWeightedGlobalControllerFactory
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 7000000
variable {p m F N : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]

theorem ThreeSum.WeightedGlobalArenaTerminalReceipt.queries_of_final (maps : Fin F→Weight m p) (τ cap K j : ℕ)
    (Q : WeightedGlobalGoodOutputCatalog.Output m) (I : Input) (A : Inputs)
    (f : Family (config p (j+1) I A 0)) (ordinal : ℕ) (μ ζ ν : ℕ→ℤ)
    (H : WeightedGlobalArenaControllerPlan.Final I f K (4^fixedLength m) F ordinal (addr I.free I.capacity 8)
      (WeightedGlobalGoodOutputCatalog.raws maps τ) (WeightedGlobalGoodOutputCatalog.wordCodes maps τ)
      (WeightedGlobalGoodOutputCatalog.mapCodes maps τ) μ ζ)
    (HC : LightWeightedGlobalPrefixFinish.Committed (config p (j+1) I A 0) (p^(j+1)) (addr I.free I.capacity 8) ζ ν)
    (hcap : 106≤I.capacity) (hO : I.requesterCount≤I.capacity)
    (hspan : A.J*(p^j)*p≤I.capacity)
    (hprefix : I.prefixFree=addr I.free I.capacity 13)
    (hbank : I.prefixFree+nb m (j+1)≤addr I.free I.capacity 16)
    (hpower : I.prefixFree+4^(WeightedGlobalArenaSourceSetup.N m (j+1))+(2*WeightedGlobalArenaSourceSetup.N m (j+1)+1)≤addr I.free I.capacity 16)
    (hcodes : Seg μ I.prefixFree ((bankCodes m (j+1)).map (fun (c : ℕ)=>(c:ℤ))))
    (hpowers : LightSubsetAddress.Powers μ (I.prefixFree+4^(WeightedGlobalArenaSourceSetup.N m (j+1))) (2*WeightedGlobalArenaSourceSetup.N m (j+1)))
    (ret : ℤ) (hheader : Seg μ (addr I.free I.capacity 1)
      (WeightedGlobalArenaHeaderAgreement.emittedHeader I p m F j Q ret)) :
    QueryReceipt maps τ cap (j+1) Q (sourceInput I A ordinal (f.candidate ordinal).data) ν := by sorry
