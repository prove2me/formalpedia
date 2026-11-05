-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalColoredConcreteFinalCall_call
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredConcreteFinalCall.call
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:48:23.561137+00:00
-- url     : https://prove2.me/theorems/e7eb588a-1898-4544-8a45-9722bf138a34
-- title:
--   call
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryColoredConcreteFinalCall.lean#L56-L105
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryColoredConcreteFinalCall.lean#L56-L105

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredFinalCall
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredFinalReady
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredConcreteFinalCall
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_ThreeSum_Karatsuba_CoeffBound_mem
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaFinalBounds_cells
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaPhaseBudget_threshold
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaPhaseFrames_output
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaQueryTimeMonotone_selected
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaScoreScan_initial
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaSelectedCollisions_selected
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum
  WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredConcreteFinalCall
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
open WeightedGlobalConcreteProfile WeightedGlobalLocalParameters WeightedGlobalColoredLoopSetup
open WeightedGlobalColoredTerminalReceipt WeightedGlobalColoredFinalReady
set_option maxHeartbeats 4000000
set_option maxRecDepth 24000
variable {κ : ℕ}
variable (P : Profile κ) (n free menu c : ℕ) (A B C : List ℤ) (initial : ℕ → ℤ)
variable [Fact (Irreducible (WeightedGlobalComputedExtensionMenu.modulus P.p (dim P n) c))]

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredConcreteFinalCall.call {lim : Limits} {d : ℕ}
    (ν : ℕ → ℤ) (loc : ℕ → ℤ) (header : ℕ) (hmeta : WeightedGlobalPreparedOriginals.Metadata n (n ^ κ) A B C)
    (hinputs : WeightedGlobalArenaFixedParameters.InputGuards P.K P.m P.radix κ n)
    (H : Ready P n free menu c A B C initial lim d ν) (T : Receipt P n free menu c A B C initial ν)
    (hloc5 : loc 5 = (header : ℤ)) (hloc6 : loc 6 = ((input P n free A B C).free : ℤ)) (hloc7 : loc 7 = (cells P n : ℤ))
    (hloc10 : loc 10 = (addr (input P n free A B C).free (cells P n) 1 : ℤ))
    (hloc12 : loc 12 = ((P.p ^ (rounds P n) : ℕ) : ℤ)) (hloc14 : loc 14 = ((2 * N P.m (rounds P n) : ℕ) : ℤ))
    (hheader :
      Seg ν header
        [(LightTernaryColorPrelude.av free n : ℤ), A.length, LightTernaryColorPrelude.bv free n, B.length,
          LightTernaryColorPrelude.cv free n, C.length])
    (hheaderSpace : header + 6 ≤ lim.space) :
    Ends lim P.color d
      (.call (252 + WeightedGlobalExecutable.reportingMain (p := P.p) P.K) LightWeightedGlobalColoredSolver.postArgs 0)
      ⟨loc, ν⟩
      (673 +
        LightWeightedGlobalPreparedPostSelection.time
          (WeightedGlobalArenaSourceSetup.setup (r := rounds P n) P.maps P.threshold P.cap P.output
            (selected P n free menu c A B C initial))
          P.H (cleanup P n free A B C) (keysB P n free menu c A B C initial) (keysC P n free menu c A B C initial))
      (fun σ =>
        σ.loc 0 =
            (if ∃ i < A.length, ∃ j < B.length, ∃ k < C.length, C.getD k 0 = A.getD i 0 + B.getD j 0 then 1 else 0 :
              ℤ) ∧
          Kept ν σ.mem (addr (input P n free A B C).free (cells P n) 6)) := by sorry
