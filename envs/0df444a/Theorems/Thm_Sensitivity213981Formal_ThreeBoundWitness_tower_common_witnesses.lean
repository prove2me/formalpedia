-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundWitness_tower_common_witnesses
-- name    : Sensitivity213981Formal.ThreeBoundWitness.tower_common_witnesses
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-26T18:39:10.500293+00:00
-- url     : https://prove2.me/theorems/ee22867d-25c8-4d73-b186-7e0edca6553f
-- title:
--   Every recursive min-max tower has common sensitivity and block witnesses
-- statement:
--   Let \(V\) be a finite nonempty vertex type, and let \(r_0,r_1,\ldots\) be a sequence of min-max recipes. For every depth \(n\), the associated Boolean tower has a common rejected input, a common accepted input with sensitive coordinates indexed by \(\mathrm{Bool}^n\), and nonempty pairwise disjoint sensitive blocks at the rejected input indexed by \(V^n\). Thus the witness construction supplies
--   \[
--   2^n\text{ common sensitive coordinates},\qquad |V|^n\text{ common sensitive blocks}.
--   \]
--   All witness transitions hold simultaneously at every level of the Boolean family.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; RecursiveLowerBounds.lean, lines 132–164.

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_RecursiveLowerBounds
import Definitions.Def_Sensitivity213981Formal_WitnessLifting
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem Sensitivity213981Formal.ThreeBoundWitness.tower_common_witnesses :
∀ {L V : Type} [inst : Fintype.{0} V] (r : Nat → Sensitivity213981Formal.ThreeBoundWitness.MinMaxRecipe L V) (v : V)
  (n : Nat),
  Nonempty.{1}
    (@Sensitivity213981Formal.ThreeBoundWitness.CommonWitnesses L
      (Sensitivity213981Formal.ThreeBoundWitness.IterProd (Prod.{0, 0} V Bool) n)
      (@Sensitivity213981Formal.ThreeBoundWitness.towerFamily L V inst r n)
      (Sensitivity213981Formal.ThreeBoundWitness.IterProd Bool n)
      (Sensitivity213981Formal.ThreeBoundWitness.IterProd V n)) := by sorry
