-- Prove2me | Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_Root_menu_and_separator_rows
-- name    : StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Root.menu_and_separator_rows
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-24T20:57:16.770383+00:00
-- url     : https://prove2.me/theorems/497fd2cc-31ef-4bfa-8931-5b0e5ef05a9e
-- title:
--   Window menus and the exact separator row tape from the five geometry tables
-- statement:
--   Fix a valid regional representative in an initialized instance. Suppose that the five regional geometry tables contain the prescribed net, owner, region, windows, and edges and that the remaining storage and control registers satisfy the geometry interface. Running the remaining menu computation and separator enumeration emits the canonical row tape and preserves the two graph indicators at their initialized addresses. For universal $c,D,b$, capacity $C$, $n$ points, and accuracy parameter $e$, its charge is at most $$cC^D n^{bE(e)},$$ where $E$ is the parameter envelope. This is the suffix needed to connect the concrete row program to the root-component theorem.
-- source:
--   Implementation of the root-component and boundary requests in Appendix A.6 of Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, https://arxiv.org/abs/2611.03547.

import Definitions.Def_StableMSR_RegionalGeometryTables
set_option linter.all false
set_option maxHeartbeats 2400000
set_option maxRecDepth 20000
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.SingleCircuit StableMSR.Recovery.SingleRAM StableMSR.Recovery.SingleWindows StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.NativeWriter.Production.Candidates StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
open scoped Classical
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical

theorem StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Root.menu_and_separator_rows :
  ∃c D b:ℕ,∀e:ℚ,0<e → e<1 →
  ∀(x:World) (s:Store),1 ≤ x.k → x.k<x.n → Ready x s → Bounded x.n s.imem →
  ∀r p:ℕ,s.ptrs 3=(r:ℤ) → s.ptrs 4=(p:ℤ) → r<x.rows*x.n → r%x.n∈WindowProfiles.keys x (r/x.n) →
  ∀u:Logical.State,Logical.Prepared x.n r (budget (e:ℝ)) (widthBound (e:ℝ)) u →
    ∀v:Logical.State, Scene.GeometryImage s.imem (WindowProfiles.piece x (r/x.n) (r%x.n)) (budget (e:ℝ)) u v →
    let d:=integerData x.n x.mem s.imem r (budget (e:ℝ))
    ∃t k,Logical.Executes x.n s.imem Scene.menuAndRows v t k ∧
      k ≤ c*x.cap^D*x.n^(b*parameterEnvelope (e:ℝ)) ∧
      t.output=rowTape CandidateRAM.Naming.name d (widthBound (e:ℝ)) ∧
      (let o:=Logical.offsets d.n (Logical.sizes d.n (budget (e:ℝ)))
       (∀j<d.n,t.heap (Logical.cursorAt o 0+j)=v.heap (Logical.cursorAt o 0+j)) ∧
       (∀j<d.n,∀z<d.n,t.heap (Logical.cursorAt o 4+(j*d.n+z))=v.heap (Logical.cursorAt o 4+(j*d.n+z)))) := by sorry
