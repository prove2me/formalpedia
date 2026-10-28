-- Prove2me | Theorems.Thm_ThreeBoundProfiles_sensitivity_le_diagonal_max
-- name    : ThreeBoundProfiles.sensitivity_le_diagonal_max
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-25T22:37:44.748417+00:00
-- url     : https://prove2.me/theorems/5e01831b-07d0-4c73-a92c-b1b48ea103be
-- title:
--   Diagonal upward and downward profiles bound sensitivity
-- statement:
--   Let \(F\) be a family of Boolean functions on a finite coordinate type, and fix a level \(i\). Suppose its diagonal upward profile is bounded by \(a\) and its diagonal downward profile by \(b\). Then
--   \[
--   s(F_i)\le\max(a,b).
--   \]
--   The upward profile bounds flips at false inputs, and the downward profile bounds flips at true inputs. This recovers ordinary sensitivity from the two directional profiles.
-- source:
--   Original Lean formalization for the Prove2Me sensitivity campaign, ProfileClosures, lines 171–187; source SHA256 351baf21cf080a3b627e16bfefb7da6dbb6f5cd892ef11e4b13bfdca1a2d3417.

import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Finset.Union
import Definitions.Def_Sensitivity213303_ProfileClosures

namespace OAI.Paper320
end OAI.Paper320
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace ThreeBoundProfiles
end ThreeBoundProfiles
open ThreeBoundProfiles
open OAI.Paper320
open scoped Classical
variable {L I : Type} [Preorder L] [Fintype I]

theorem ThreeBoundProfiles.sensitivity_le_diagonal_max (F : L → (I → Bool) → Bool) (i : L) (a b : ℕ)
    (ha : ABound F i i a) (hb : BBound F i i b) : sensitivity (F i) ≤ max a b := by sorry
