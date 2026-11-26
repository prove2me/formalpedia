-- Prove2me | Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_Root_write_single_separator_level
-- name    : StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Root.write_single_separator_level
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-25T05:51:18.104301+00:00
-- url     : https://prove2.me/theorems/1bde2d53-833e-4e29-8fe4-b5dc04e0c34a
-- title:
--   The separator traversal at a fixed component size
-- statement:
--   At one component-size level, start with the established regional geometry and menu tables and any output prefix whose length matches the output register. The actual cut traversal appends exactly the instructions for components of that size in the mathematical row tape, preserving the permanent tables and the register and cursor invariants required for the next level. Its running time is bounded uniformly by $c\,\mathrm{cap}^D n^{bE(\varepsilon)}$.
-- source:
--   Implementation of the root-component and boundary requests in Appendix A.6 of Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, https://arxiv.org/abs/2611.03547.

import Definitions.Def_StableMSR_SeparatorLevel
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

theorem StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Root.write_single_separator_level :
  ∃c D b:ℕ,∀e:ℚ,0<e → e<1 →
  ∀(x:World) (s:Store),1 ≤ x.k → x.k<x.n → Ready x s → Bounded x.n s.imem →
  ∀r p:ℕ,s.ptrs 3=(r:ℤ) → s.ptrs 4=(p:ℤ) → r<x.rows*x.n → r%x.n∈WindowProfiles.keys x (r/x.n) →
  ∀u:Logical.State,Logical.Prepared x.n r (budget (e:ℝ)) (widthBound (e:ℝ)) u →
    ∀v:Logical.State, Scene.GeometryImage s.imem (WindowProfiles.piece x (r/x.n) (r%x.n)) (budget (e:ℝ)) u v →
    ∀z:Logical.State, Scene.RegionalMenus s.imem (WindowProfiles.piece x (r/x.n) (r%x.n)) (budget (e:ℝ)) v z →
    ∀ level < x.n, ∀ a : Logical.State,
      Scene.SeparatorLevels.Between z a → a.reg 259=(level:ℤ) →
      let d:=integerData x.n x.mem s.imem r (budget (e:ℝ))
      ∃t k, Logical.Executes x.n s.imem Logical.src_all_cuts a t k ∧
        k ≤ c*x.cap^D*x.n^(b*parameterEnvelope (e:ℝ)) ∧
        Scene.SeparatorLevels.Between z t ∧
        t.output=a.output++Scene.SeparatorLevels.levelTape d (widthBound (e:ℝ)) level := by sorry
