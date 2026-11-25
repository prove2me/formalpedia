-- Prove2me | Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_Scene_BlockRows_distinct_block_representatives
-- name    : StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.BlockRows.distinct_block_representatives
-- status  : Open
-- author  : @lreyzin
-- created : 2026-11-25T04:48:30.025858+00:00
-- url     : https://prove2.me/theorems/ca4b4afd-5aa6-45e1-8188-7ccce4bd82ec
-- title:
--   Least-indexed seeds represent the distinct blocks of a window
-- statement:
--   Let $W$ be a window and let $C_i$ be the block produced by its seed $i$ for a fixed candidate word in the integer distance oracle. Write $R$ for the least seed index of each distinct block and $P$ for the deduplicated list of blocks. Then
--   $$\{C_i:i\in R\}=\operatorname{set}(P),\qquad C_i=C_j\ (i,j\in R)\ \Longrightarrow\ i=j.$$
--   Every representative is a valid point index. A seed belongs to $R$ exactly when no earlier representative produces the same block. These identities connect the order in which the program visits seeds with the family used in the window feasibility test.
-- source:
--   Native candidate enumeration in Appendix A.6, Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, https://arxiv.org/abs/2611.03547.

import Definitions.Def_StableMSR_VertexBlockRows
set_option linter.all false
set_option maxHeartbeats 2400000
set_option maxRecDepth 20000
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.SingleCircuit StableMSR.Recovery.SingleRAM StableMSR.Recovery.SingleWindows StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.NativeWriter.Production.Candidates StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
open scoped Classical
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical
set_option maxHeartbeats 4100000
set_option maxRecDepth 35000
set_option autoImplicit false
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.BlockRows

theorem StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.BlockRows.distinct_block_representatives
    {n : ℕ} (m : ℤ → ℤ) (W : Cluster n) (h c : ℕ) :
    let C := rowBlock m W h c
    let R := representatives W C
    (∀ i ∈ R, i < n) ∧
    (Bits.blocks m W h c).toFinset = R.image C ∧
    (∀ i ∈ R, ∀ j ∈ R, C i = C j → i = j) ∧
    (∀ p ∈ W, p.val ∈ R ↔ ¬∃ i ∈ R, i < p.val ∧ C i = C p.val)
 := by sorry
