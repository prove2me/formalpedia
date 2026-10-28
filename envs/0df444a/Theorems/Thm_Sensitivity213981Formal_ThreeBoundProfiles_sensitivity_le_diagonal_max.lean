-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundProfiles_sensitivity_le_diagonal_max
-- name    : Sensitivity213981Formal.ThreeBoundProfiles.sensitivity_le_diagonal_max
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-26T18:31:40.185359+00:00
-- url     : https://prove2.me/theorems/8e2f4eeb-c041-4234-a4f5-2545123a95cb
-- title:
--   Diagonal upward and downward profiles bound sensitivity
-- statement:
--   Let \(F\) be a family of Boolean functions on a finite coordinate type, and fix a level \(i\). Suppose its diagonal upward profile is bounded by \(a\) and its diagonal downward profile by \(b\). Then
--   \[
--   s(F_i)\le\max(a,b).
--   \]
--   The upward profile bounds flips at false inputs, and the downward profile bounds flips at true inputs. This recovers ordinary sensitivity from the two directional profiles.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; ProfileClosures.lean, lines 171–187.

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_ProfileClosures
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem Sensitivity213981Formal.ThreeBoundProfiles.sensitivity_le_diagonal_max :
∀ {L I : Type} [Preorder.{0} L] [inst : Fintype.{0} I] (F : L → (I → Bool) → Bool) (i : L) (a b : Nat)
  (ha : @Sensitivity213981Formal.ThreeBoundProfiles.ABound L I inst F i i a)
  (hb : @Sensitivity213981Formal.ThreeBoundProfiles.BBound L I inst F i i b),
  @LE.le.{0} Nat instLENat (@OAI.Paper320.sensitivity I inst (F i)) (@Max.max.{0} Nat Nat.instMax a b) := by sorry
