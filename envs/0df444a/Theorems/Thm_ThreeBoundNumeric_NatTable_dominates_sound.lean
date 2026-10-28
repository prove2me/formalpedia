-- Prove2me | Theorems.Thm_ThreeBoundNumeric_NatTable_dominates_sound
-- name    : ThreeBoundNumeric.NatTable.dominates_sound
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-25T22:42:55.025675+00:00
-- url     : https://prove2.me/theorems/342921a9-9b8f-42ac-97f9-9cc0a88da95c
-- title:
--   Soundness of multiplicative comparison for finite lookup tables
-- statement:
--   Let a and b be natural-valued binary lookup tables, and let c be a natural number. If the recursive comparison dominates(c,a,b) succeeds, then a(i) ≤ c b(i) for every natural-number index i. The assertion applies to all indices, including those routed to constant leaves outside a finite list of explicitly distinguished indices.
-- source:
--   Original Lean formalization for the Prove2Me sensitivity campaign, NatTableChecks, lines 42–81; source SHA256 1697051482b0f8234dc028eba3f66c46520034c6c4f61c9091cebfe9a7e6dfeb.

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

theorem ThreeBoundNumeric.NatTable.dominates_sound (factor : ℕ) (a b : NatTable)
    (h : dominates factor a b=true) : ∀ i, a.get i≤factor*b.get i := by sorry
