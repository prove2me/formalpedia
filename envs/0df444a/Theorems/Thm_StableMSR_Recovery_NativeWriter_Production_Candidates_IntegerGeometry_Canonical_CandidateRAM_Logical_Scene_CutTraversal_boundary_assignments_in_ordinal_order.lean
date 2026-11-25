-- Prove2me | Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_Scene_CutTraversal_boundary_assignments_in_ordinal_order
-- name    : StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal.boundary_assignments_in_ordinal_order
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-25T13:03:02.844585+00:00
-- url     : https://prove2.me/theorems/b65e581d-d7f0-451b-9e5d-82ddc9f0e1d9
-- title:
--   The boundary ordinals enumerate exactly the feasible assignments in order
-- statement:
--   For a region with prepared geometry and candidate tables, decode each ordinal in increasing order, reading its base digits from the right end of the boundary list. Read the word and its vertex feasibility bit from the actual preserved heap. Keeping exactly the ordinals that pass gives the reference list of boundary assignments, with the same order and multiplicities.
-- source:
--   S. Ravichandran and L. Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, arXiv:2611.03547, Appendix A.4 and A.6. Implementation lemma for the mission’s regional separator compiler.

import Definitions.Def_StableMSR_EligibleSeparatorRows
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

open Scene.CutTraversal Scene.SeparatorLevels TightLanguage

theorem StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal.boundary_assignments_in_ordinal_order (x : World) (s : Store) (r h w : ℕ)
    (u v z a : Logical.State) (hn : 0 < x.n) (prep : Prepared x.n r h w u)
    (geometry : Scene.GeometryImage s.imem (WindowProfiles.piece x (r/x.n) (r%x.n)) h u v)
    (menus : Scene.RegionalMenus s.imem (WindowProfiles.piece x (r/x.n) (r%x.n)) h v z)
    (preserved : Between z a) (cut : List ℕ) (bounded : ∀ p ∈ cut, p < x.n) :
    let base := (a.reg 70).toNat
    let word := fun i => (a.heap ((a.reg 76).toNat+i)).toNat
    let permitted := fun p i => decide (1 ≤ a.heap ((a.reg 81).toNat+(p*base+i)))
    (List.range (base^cut.length)).filterMap ((cut.reverse.foldr (fun v (k : ℕ → Option Assignment) q =>
        if permitted v (q%base) then (k (q/base)).map (fun t => t++[(v,word (q%base))]) else none)
        (fun _ => some []))) =
      assignments (integerData x.n x.mem s.imem r h) cut := by sorry
