-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalColoredNonemptyExecution_ends
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredNonemptyExecution.ends
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:32:57.611024+00:00
-- url     : https://prove2.me/theorems/fb31259d-8e21-485a-8c3d-a105a53f0621
-- title:
--   ends
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryColoredNonemptyExecution.lean#L37-L121
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryColoredNonemptyExecution.lean#L37-L121

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredLoopCall
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredFinishCall
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredPreparationFields
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredInitializationResources
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredProgramIdentity
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredNonemptyExecution
import Theorems.Thm_ThreeSum_Karatsuba_CoeffBound_mem
import Definitions.Def_WeightedCache3SUM_Alias_2355ab610500aa6c
import Theorems.Thm_ThreeSum_LightTernaryFixedChannelLoop_ends
import Theorems.Thm_ThreeSum_ReportingHostRelocation_ends
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalPrefixFinish_ends
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaFixedParameters_cutoff
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaScoreScan_initial

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredNonemptyExecution
open Light WeightedGlobalConcreteProfile WeightedGlobalColoredLoopSetup WeightedGlobalArenaLayout WeightedGlobalLocalParameters
open LightWeightedGlobalColoredSolver LightWeightedGlobalColoredInitializationProof
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
variable {κ : ℕ}

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredNonemptyExecution.ends {lim : Limits} {d : ℕ} (P : Profile κ) (n free menu c : ℕ)
    (A B C oldA oldB oldC : List ℤ) (initial : ℕ→ℤ) (locals : List ℤ)
    [Fact (Irreducible (WeightedGlobalComputedExtensionMenu.modulus P.p (dim P n) c))]
    (hcutoff : P.cutoff≤n) (hneed : (P.colorNeed n (n^κ)).Ok lim free d)
    (hmeta : WeightedGlobalPreparedOriginals.Metadata n (n^κ) A B C)
    (NA : LightTernaryColorPrelude.Normalized initial (LightTernaryColorPrelude.av free n) n oldA A)
    (NB : LightTernaryColorPrelude.Normalized initial (LightTernaryColorPrelude.bv free n) n oldB B)
    (NC : LightTernaryColorPrelude.Normalized initial (LightTernaryColorPrelude.cv free n) n oldC C)
    (hheader : Seg initial (LightWeightedGlobalColorPreparation.headerAt free n (LightColorParametersCosts.width n))
      (LightWeightedGlobalColorPreparationProof.header free n (n^κ) (rounds P n) (J P n) (q P n) menu A B C))
    (hOriginals : WeightedGlobalArenaPrefixInputs.Originals (input P n free A B C) (arrays P n free menu A B C)
      (q P n*q P n) P.radix P.radix n
      (WeightedGlobalComputedExtensionMenu.functional (p:=P.p) (c:=c) (dim_pos P n))
      (WeightedGlobalArenaFamilyBudget.seedAt (WeightedGlobalComputedExtensionMenu.seeds (p:=P.p) (d:=dim P n) (c:=c)))
      (WeightedGlobalArenaSelectedSigned.left (n^κ) P.radix (J P n) (fun i=>B.getD i 0))
      (WeightedGlobalArenaSelectedSigned.right (n^κ) P.radix (J P n) (fun i=>C.getD i 0))
      (WeightedGlobalArenaSelectedSigned.requester (n^κ) P.radix (J P n) (fun i=>A.getD i 0)) initial)
    (h1 : frame locals 1=(n:ℤ))
    (h5 : frame locals 5=(LightWeightedGlobalColorPreparation.headerAt free n (LightColorParametersCosts.width n):ℤ)) :
    let S:=setup P n free menu c A B C initial
    Ends lim P.color d (initChunk P.p (4^fixedLength P.m) P.F (tail P)) ⟨frame locals,initial⟩
      (LightWeightedGlobalArenaTemplate.time P.allocation.E+LightTernaryInitialBudgets.time P.K+
        S.initTime+postTime P n free menu c A B C initial+8000)
      (fun σ=>σ.loc 0=(if ∃i<A.length,∃j<B.length,∃k<C.length,
          C.getD k 0=A.getD i 0+B.getD j 0 then 1 else 0:ℤ) ∧
        Kept initial σ.mem (input P n free A B C).free) := by sorry
