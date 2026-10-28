-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundNumeric_NatTable_dominates_sound
-- name    : Sensitivity213981Formal.ThreeBoundNumeric.NatTable.dominates_sound
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T01:31:43.547013+00:00
-- url     : https://prove2.me/theorems/7b543cda-771e-4326-8737-6b9c5e95fffb
-- title:
--   Soundness of multiplicative comparison for finite lookup tables
-- statement:
--   Let a and b be natural-valued binary lookup tables, and let c be a natural number. If the recursive comparison dominates(c,a,b) succeeds, then a(i) ≤ c b(i) for every natural-number index i. The assertion applies to all indices, including those routed to constant leaves outside a finite list of explicitly distinguished indices.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; NatTableChecks.lean, lines 42–81.

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_NatTableChecks
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.FinRange
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem Sensitivity213981Formal.ThreeBoundNumeric.NatTable.dominates_sound :
∀ (factor : Nat) (a b : Sensitivity213981Formal.ThreeBoundNumeric.NatTable)
  (h : @Eq.{1} Bool (Sensitivity213981Formal.ThreeBoundNumeric.NatTable.dominates factor a b) Bool.true) (i : Nat),
  @LE.le.{0} Nat instLENat (Sensitivity213981Formal.ThreeBoundNumeric.NatTable.get a i)
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) factor
      (Sensitivity213981Formal.ThreeBoundNumeric.NatTable.get b i)) := by sorry
