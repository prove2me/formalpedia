-- Prove2me | Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_Scene_menu_word_schedule_and_digits
-- name    : StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.menu_word_schedule_and_digits
-- status  : Open
-- author  : @lreyzin
-- created : 2026-11-24T20:59:47.707825+00:00
-- url     : https://prove2.me/theorems/28f43721-9993-4d7e-b5e3-7ef34db6ab45
-- title:
--   The menu program enumerates canonical words in order and decodes every digit
-- statement:
--   Let $H=h+1$ and $R=n^{2H}$. At position $i=gR+u$ with $g<H$ and $u<R$, the menu program stores exactly the $i$th word of the canonical list, $$c=uH+g.$$ The register passed to the vertex computation contains $c$. The corresponding vertex decoder writes $2H$ digits into its scratch array. Digit $j$ is $$\left\lfloor u/n^j\right\rfloor\bmod n.$$ After the last digit the quotient is zero. Each stage preserves the output and the heap outside its destination. Their respective charges are at most $180+22H$ and $65+8u+2H(155+16u)$.
-- source:
--   Implementation of the root-component and boundary requests in Appendix A.6 of Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, https://arxiv.org/abs/2611.03547.

import Definitions.Def_StableMSR_InitializedSeparatorTraversal
set_option linter.all false
set_option maxHeartbeats 2400000
set_option maxRecDepth 20000
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.SingleCircuit StableMSR.Recovery.SingleRAM StableMSR.Recovery.SingleWindows StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.NativeWriter.Production.Candidates StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
open scoped Classical
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical

theorem StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.menu_word_schedule_and_digits (n h g u : ℕ) (m : ℤ → ℤ)
    (hn : 0<n) (hg : g<h+1) (hu : u<CartesianBallRows.rows n (h+1)) :
  (∀ (base : ℕ) (s : Logical.State), s.reg 6=1 → s.reg 68=((h+1:ℕ):ℤ) →
    s.reg 69=(CartesianBallRows.rows n (h+1):ℤ) → s.reg 76=(base:ℤ) →
    s.reg 196=((g*CartesianBallRows.rows n (h+1)+u:ℕ):ℤ) →
    let R:=CartesianBallRows.rows n (h+1)
    let i:=g*R+u
    let c:=SingleCodes.encode h g u
    let dispatch:=match (Logical.listOf ((Logical.listOf Logical.src_build_geometry)[24]?.getD .skip))[3]? with
      | some (Logical.Program.loop _ _ body) => Logical.chain ((Logical.listOf ((Logical.listOf body)[0]?.getD .skip)).take 6)
      | _ => Logical.Program.skip
    (SingleCodes.words n h)[i]?=some c ∧
      ∃t k, Logical.Executes n m dispatch s t k ∧ k≤180+22*(h+1) ∧
        t.reg 199=(c:ℤ) ∧ t.heap=Function.update s.heap (base+i) (c:ℤ) ∧ t.output=s.output ∧ t.closed=s.closed) ∧
  (∀ (base : ℕ) (s : Logical.State), s.reg 6=1 → s.reg 64=(n:ℤ) → s.reg 68=((h+1:ℕ):ℤ) →
    s.reg 163=(SingleCodes.encode h g u:ℤ) → s.reg 166=(base:ℤ) →
    let L:=2*(h+1)
    ∃ t k, Logical.Executes n m (Logical.chain (((Logical.listOf Logical.src_data_for_vertex).drop 7).take 4)) s t k ∧
      k ≤ 65+8*u+L*(155+16*u) ∧ t.reg 167=0 ∧
      (∀j<L,t.heap (base+j)=(CartesianBallRows.digit n u j:ℤ)) ∧
      (∀z,z<base ∨ base+L≤z → t.heap z=s.heap z) ∧ t.output=s.output ∧ t.closed=s.closed) := by sorry
