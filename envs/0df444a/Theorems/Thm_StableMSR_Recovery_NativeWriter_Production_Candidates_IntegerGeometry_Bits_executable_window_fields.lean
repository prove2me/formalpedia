-- Prove2me | Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Bits_executable_window_fields
-- name    : StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Bits.executable_window_fields
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-24T00:29:57.585048+00:00
-- url     : https://prove2.me/theorems/40e12830-abc1-4bb1-b6bd-83a57110c600
-- title:
--   Executable integer computation of all menu and compatibility entries
-- statement:
--   Pure integer calculations reproduce every active flag, oriented edge, ordered menu and local compatibility bit of the regional instance. The same program computes each owned block and its point memberships. After reading masks as point sets, the two block lists are permutations, including multiplicities. This holds for every integer distance table.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Appendix A.6, pp. 21–22, https://arxiv.org/abs/2611.03547. Quantitative implementation lemma for the mission’s dense regional circuit.

import Definitions.Def_StableMSR_IntegerWindowCandidates
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.SingleCircuit

open StableMSR.Recovery.NativeWriter.Production.Candidates

open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry

theorem StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Bits.executable_window_fields
    (x:World) (m:ℤ→ℤ) (r h:ℕ) :
    let t:=Bits.normalized m (Bits.piece x.n x.mem (r/x.n) (r%x.n)) h
    let d:=data x m r h
    t.n=d.n ∧ t.active=d.active ∧ t.edge=d.edge ∧ t.menu=d.menu ∧ t.test=d.test ∧
      ∀a c,Bits.MasksAgree (t.owned a c) (d.owned a c) := by sorry
