-- Prove2me | Theorems.Thm_ThreeBoundNumeric_NatTable_lowerCheck_sound
-- name    : ThreeBoundNumeric.NatTable.lowerCheck_sound
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-25T22:43:02.890082+00:00
-- url     : https://prove2.me/theorems/18c4bba3-1c01-46ea-86f8-d4a980e9a179
-- title:
--   Soundness of uniform lower bounds for finite lookup tables
-- statement:
--   For a natural-valued binary lookup table T and a natural number b, a successful recursive lowerCheck(b,T) certifies b ≤ T(i) for every natural-number index i.
-- source:
--   Original Lean formalization for the Prove2Me sensitivity campaign, NatTableChecks, lines 15–27; source SHA256 1697051482b0f8234dc028eba3f66c46520034c6c4f61c9091cebfe9a7e6dfeb.

import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Finset.Union
import Mathlib.Data.List.FinRange
import Mathlib.Tactic.Ring
import Definitions.Def_Sensitivity213303_FlatProfiles
import Definitions.Def_Sensitivity213303_FullProfileClosure
import Definitions.Def_Sensitivity213303_NatTableChecks
import Definitions.Def_Sensitivity213303_NumericExpressions
import Definitions.Def_Sensitivity213303_ProfileClosures


set_option autoImplicit false
namespace ThreeBoundNumeric
end ThreeBoundNumeric
open ThreeBoundNumeric
namespace ThreeBoundNumeric.NatTable
end ThreeBoundNumeric.NatTable
open ThreeBoundNumeric.NatTable

theorem ThreeBoundNumeric.NatTable.lowerCheck_sound (bound : ℕ) (table : NatTable)
    (h : lowerCheck bound table=true) : ∀ i, bound≤table.get i := by sorry
