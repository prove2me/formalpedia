-- Prove2me | Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_matrix_and_row_scans
-- name    : StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.matrix_and_row_scans
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-24T02:26:53.393973+00:00
-- url     : https://prove2.me/theorems/a8f03c7f-133c-4961-a9d0-df92292c96dc
-- title:
--   The three source routines read matrix entries, locate least points and compare rows exactly
-- statement:
--   The actual matrix-read procedure returns the arbitrary directed input word at $(i,j)$ in at most $50+6n$ charges. The least-marked-point scan returns the first positive word or $n$ when absent in at most $15+95n$. The two-row scan returns exactly the equality bit for all $n$ integer words in at most $17+150n$. All three preserve the entire scratch array and the output stream.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Appendix A.6, pp. 21–22, https://arxiv.org/abs/2611.03547. Quantitative implementation lemma for the mission’s dense regional circuit.

import Definitions.Def_StableMSR_LogicalCandidateProgram
set_option linter.all false
set_option maxHeartbeats 2400000
set_option maxRecDepth 20000
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.SingleCircuit StableMSR.Recovery.SingleRAM StableMSR.Recovery.SingleWindows StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.NativeWriter.Production.Candidates StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
open scoped Classical
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical

theorem StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.matrix_and_row_scans :
    (∀(n i j:ℕ) (input:ℤ → ℤ) (s:State) (one:s.reg 6=1) (size:s.reg 64=(n:ℤ))
    (ri:s.reg 159=(i:ℤ)) (rj:s.reg 160=(j:ℤ)),∃t k,Executes n input src_imat s t k ∧ k ≤ 50+6*n ∧ t.reg 161=input (cell 6 (i*n+j)) ∧
      t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed) ∧
    (∀(n base:ℕ) (m:ℤ → ℤ) (s:State) (one:s.reg 6=1) (size:s.reg 64=(n:ℤ)) (ptr:s.reg 144=(base:ℤ)),∃t k,Executes n m src_first s t k ∧ k ≤ 15+95*n ∧
    t.reg 147=(((List.range n).filter (fun i=>decide (1 ≤ s.heap (base+i)))).headD n:ℕ) ∧
    t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed) ∧
    (∀(n a b:ℕ) (m:ℤ → ℤ) (s:State) (one:s.reg 6=1) (size:s.reg 64=(n:ℤ))
    (left:s.reg 148=(a:ℤ)) (right:s.reg 149=(b:ℤ)),∃t k,Executes n m src_equal_rows s t k ∧ k ≤ 17+150*n ∧
    (t.reg 152=1 ↔ ∀i<n,s.heap (a+i)=s.heap (b+i)) ∧
    (t.reg 152=0 ∨ t.reg 152=1) ∧ t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed) := by sorry
