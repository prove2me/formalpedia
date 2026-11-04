-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalColoredFinishCall_finish
-- name    : ThreeSum.WeightedGlobalColoredFinishCall.finish
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T03:37:00.460612+00:00
-- url     : https://prove2.me/theorems/4653c05d-2afd-44d4-9ad4-a059c1d2a347
-- title:
--   Weighted Global Colored Finish Call: finish
-- statement:
--   The last two assignments and final reporter call consume only the
--   executed loop's invariant and the actual original preprocessing records.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredFinishCall.lean#L49-L122
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredFinishCall.lean#L49-L122

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryColoredConcreteFinalCall
import Definitions.Def_Submission_Weighted_Global_TernaryColoredLookupDepth
import Definitions.Def_Submission_Weighted_Global_TernaryColoredFinishCall
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_ThreeSum_Karatsuba_CoeffBound_mem
import Theorems.Thm_ThreeSum_LightWeightedGlobalPreparedPostSelection_Inputs_finish
import Theorems.Thm_ThreeSum_TernarySourceExecutionFactory_Seed_finish
import Theorems.Thm_ThreeSum_WeightedGlobalArenaFinalBounds_cells
import Theorems.Thm_ThreeSum_WeightedGlobalArenaFixedParameters_cutoff
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPhaseBudget_threshold
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPhaseFrames_output
import Theorems.Thm_ThreeSum_WeightedGlobalArenaQueryTimeMonotone_selected
import Theorems.Thm_ThreeSum_WeightedGlobalArenaScoreScan_initial
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSelectedCollisions_selected
import Theorems.Thm_ThreeSum_WeightedGlobalColoredConcreteFinalCall_call
import Theorems.Thm_ThreeSum_WeightedSourceCountExecutionFactory_Seed_finish
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalColoredFinishCall
open Light WeightedGlobalConcreteProfile WeightedGlobalColoredLoopSetup WeightedGlobalArenaLayout
open WeightedGlobalLocalParameters WeightedGlobalArenaSourceSetup WeightedGlobalColoredTerminalReceipt
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
variable {κ : ℕ}

theorem ThreeSum.WeightedGlobalColoredFinishCall.finish {lim : Limits} {d header : ℕ} (P : Profile κ)
    (n free menu c : ℕ) (A B C oldA oldB oldC : List ℤ) (initial ν loc : ℕ → ℤ)
    [Fact (Irreducible (WeightedGlobalComputedExtensionMenu.modulus P.p (dim P n) c))]
    (NA : LightTernaryColorPrelude.Normalized initial (LightTernaryColorPrelude.av free n) n oldA A)
    (NB : LightTernaryColorPrelude.Normalized initial (LightTernaryColorPrelude.bv free n) n oldB B)
    (NC : LightTernaryColorPrelude.Normalized initial (LightTernaryColorPrelude.cv free n) n oldC C)
    (hmeta : WeightedGlobalPreparedOriginals.Metadata n (n ^ κ) A B C) (hcutoff : P.cutoff ≤ n)
    (hok :
      (WeightedGlobalArenaAllocationResources.need P.allocation n (n ^ κ)).Ok lim (input P n free A B C).free (d + 3))
    (Hloop :
      WeightedGlobalArenaLoop.Invariant (WeightedGlobalColoredLoopSetup.setup P n free menu c A B C initial)
        (rounds P n) ν)
    (hheader :
      Seg initial header
        (LightWeightedGlobalColorPreparationProof.header free n (n ^ κ) (rounds P n) (J P n) (q P n) menu A B C))
    (hheaderEnd : header + 19 ≤ (input P n free A B C).free) (h5 : loc 5 = (header : ℤ))
    (h6 : loc 6 = ((input P n free A B C).free : ℤ)) (h7 : loc 7 = (cells P n : ℤ))
    (h10 : loc 10 = (addr (input P n free A B C).free (cells P n) 1 : ℤ))
    (h12 : loc 12 = ((P.p ^ (rounds P n) : ℕ) : ℤ)) :
    Ends lim P.color d
      (_root_.Light.Stmt.seq
        (.set 13
          ((_root_.Light.Expr.op _root_.Light.Op.mul) (k (fixedLength P.m)) (LightWeightedGlobalColoredSolver.H 15)))
        (_root_.Light.Stmt.seq (.set 14 ((_root_.Light.Expr.op _root_.Light.Op.mul) (k 2) (v 13)))
          (.call (252 + WeightedGlobalExecutable.reportingMain (p := P.p) P.K) LightWeightedGlobalColoredSolver.postArgs
            0)))
      ⟨loc, ν⟩
      (1000 +
        LightWeightedGlobalPreparedPostSelection.time
          (WeightedGlobalArenaSourceSetup.setup (r := rounds P n) P.maps P.threshold P.cap P.output
            (WeightedGlobalColoredFinalReady.selected P n free menu c A B C initial))
          P.H (WeightedGlobalColoredFinalReady.cleanup P n free A B C) (keysB P n free menu c A B C initial)
          (keysC P n free menu c A B C initial))
      (fun σ =>
        σ.loc 0 =
            (if ∃ i < A.length, ∃ j < B.length, ∃ k < C.length, C.getD k 0 = A.getD i 0 + B.getD j 0 then 1 else 0 :
              ℤ) ∧
          Kept initial σ.mem (input P n free A B C).free) := by sorry
