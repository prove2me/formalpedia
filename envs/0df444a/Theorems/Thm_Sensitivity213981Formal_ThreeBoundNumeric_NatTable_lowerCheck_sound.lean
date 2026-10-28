-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundNumeric_NatTable_lowerCheck_sound
-- name    : Sensitivity213981Formal.ThreeBoundNumeric.NatTable.lowerCheck_sound
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T01:31:46.160769+00:00
-- url     : https://prove2.me/theorems/6f0ade9e-8d01-4b1a-aab4-760a9ee771db
-- title:
--   Soundness of uniform lower bounds for finite lookup tables
-- statement:
--   For a natural-valued binary lookup table T and a natural number b, a successful recursive lowerCheck(b,T) certifies b ≤ T(i) for every natural-number index i.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; NatTableChecks.lean, lines 15–27.

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

theorem Sensitivity213981Formal.ThreeBoundNumeric.NatTable.lowerCheck_sound :
∀ (bound : Nat) (table : Sensitivity213981Formal.ThreeBoundNumeric.NatTable)
  (h : @Eq.{1} Bool (Sensitivity213981Formal.ThreeBoundNumeric.NatTable.lowerCheck bound table) Bool.true) (i : Nat),
  @LE.le.{0} Nat instLENat bound (Sensitivity213981Formal.ThreeBoundNumeric.NatTable.get table i) := by sorry
