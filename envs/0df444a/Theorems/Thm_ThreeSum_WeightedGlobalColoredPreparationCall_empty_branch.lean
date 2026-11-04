-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalColoredPreparationCall_empty_branch
-- name    : ThreeSum.WeightedGlobalColoredPreparationCall.empty_branch
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T22:28:34.493049+00:00
-- url     : https://prove2.me/theorems/ba3f23ae-7b66-4d88-9b3b-074a4c5e0df3
-- title:
--   Weighted Global Colored Preparation Call: empty branch
-- statement:
--   The zero-preparation branch returns immediately with the required
--   original-color answer, regardless of the unexecuted nonempty branch.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredPreparationCall.lean#L104-L120
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredPreparationCall.lean#L104-L120

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryColoredSolverNeed
import Definitions.Def_Submission_Weighted_Global_LightTernaryColoredSolver
import Definitions.Def_Submission_Weighted_Global_TernaryColoredPreparationCall
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_ThreeSum_Karatsuba_CoeffBound_mem

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalColoredPreparationCall
open Light LightWeightedGlobalColoredSolver
set_option maxHeartbeats 2000000
set_option maxRecDepth 24000

theorem ThreeSum.WeightedGlobalColoredPreparationCall.empty_branch {lim : Limits} {P : Program} {d n free U R J q menu radix : ℕ}
    {p : Coloring.Parameter (LightColorParametersCosts.width n)} {x : Fin n→ℤ}
    (loc μ ν : ℕ→ℤ) (tail : Stmt)
    (hout : LightWeightedGlobalColorPreparationProof.Output μ ν free U R J q menu radix p x 0)
    (hzero : loc 5=0) (hw : (0:ℤ)≤lim.word) :
    Ends lim P d (.ite (v 5 =' k 0) (.set 0 (k 0)) tail) ⟨loc,ν⟩ 100
      (fun σ=>σ.loc 0=0 ∧ ¬ColorClassLists.witness p x ∧ Kept μ σ.mem free) := by sorry
