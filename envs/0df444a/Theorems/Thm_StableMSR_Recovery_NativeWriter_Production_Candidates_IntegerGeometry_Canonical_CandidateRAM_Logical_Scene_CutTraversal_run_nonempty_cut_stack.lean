-- Prove2me | Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_Scene_CutTraversal_run_nonempty_cut_stack
-- name    : StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal.run_nonempty_cut_stack
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-25T12:30:23.195528+00:00
-- url     : https://prove2.me/theorems/9f967385-1d32-448a-843b-26f3331a7472
-- title:
--   Depth-first traversal from the initialized empty separator
-- statement:
--   Given a correct bounded visitor, the initialized controller visits precisely the nonempty separators in reference order. If one visit costs at most $V$, the controller takes at most $1000(V+1)(n+1)^{\min(w,n)+2}$ steps and preserves the regional tables.
-- source:
--   S. Ravichandran and L. Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, arXiv:2611.03547, Appendix A.4 and A.6. Implementation lemma for the mission’s regional separator compiler.

import Definitions.Def_StableMSR_CutTraversal
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

theorem StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal.run_nonempty_cut_stack :
∀(d : SingleCircuit.Instance) (w level V base : ℕ) (m : ℤ→ℤ) (z a : Logical.State),
    0<d.n → Scene.CutTraversal.TraversalData d w z → Scene.SeparatorLevels.Between z a →
    (z.reg 8).toNat ≤ base → Scene.CutTraversal.RootStack d.n level base a → Scene.CutTraversal.Visits d w level m z V →
    ∃t k, Logical.Executes d.n m Scene.CutTraversal.remainingProgram a t k ∧
      k ≤ 1000*(V+1)*(d.n+1)^(min w d.n+2) ∧ Scene.SeparatorLevels.Between z t ∧
      t.output=a.output++((TightLanguage.cuts (TightLanguage.vertices d) (min w d.n)).drop 1).flatMap
        (Scene.CutTraversal.cutTape d level) := by sorry
