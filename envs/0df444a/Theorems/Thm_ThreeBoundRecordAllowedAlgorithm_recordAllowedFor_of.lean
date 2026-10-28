-- Prove2me | Theorems.Thm_ThreeBoundRecordAllowedAlgorithm_recordAllowedFor_of
-- name    : ThreeBoundRecordAllowedAlgorithm.recordAllowedFor_of
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-25T22:41:34.270823+00:00
-- url     : https://prove2.me/theorems/07722d61-f97f-456e-9ace-68ecca3e9037
-- title:
--   Semantic exclusions imply the pair-specific record filter
-- statement:
--   Let \(a,c\) be weak and strong recipe entries, let \(r\) be a \(q\le2\) record, and assume its general cap filter accepts. Suppose every tier \(k\le c.\mathrm{tolerance}\) satisfies the following additional restrictions: when \(k<a.\mathrm{tolerance}\) and \(a.\mathrm{threshold}(k+1)\le c.\mathrm{threshold}(k)\), the relevant guard and overlap counts vanish; when a pure positive count \(r(k)\) is nonzero, \(c.\mathrm{guard}\) differs from the applicable weak/previous-strong target barrier. Then
--   \[
--   \operatorname{recordAllowedFor}(\mathrm{caps},a,c,r)=\mathrm{true}.
--   \]
--   This separates the mathematical exclusion hypotheses from their executable Boolean filter.
-- source:
--   Original Lean formalization for the Prove2Me sensitivity campaign, RecordAllowedAlgorithm, lines 24–53; source SHA256 0890dfe0ea7f207a310834ba1791f0d3210cfcaa03b2df0efac350fe6fd48bed.

import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Finset.Union
import Mathlib.Data.List.FinRange
import Mathlib.Tactic.Ring
import Definitions.Def_Sensitivity213303_FullProfileClosure
import Definitions.Def_Sensitivity213303_NumericExpressions
import Definitions.Def_Sensitivity213303_ProfileClosures
import Definitions.Def_Sensitivity213303_Q2RawExpressions

namespace ThreeBoundNumeric
end ThreeBoundNumeric
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace ThreeBoundRecordAllowedAlgorithm
end ThreeBoundRecordAllowedAlgorithm
open ThreeBoundRecordAllowedAlgorithm
open ThreeBoundNumeric

theorem ThreeBoundRecordAllowedAlgorithm.recordAllowedFor_of (caps : Caps) (a c : Entry) (r : Q2Record)
    (hallowed : allowedRecord caps c.tolerance r = true)
    (hguard : ∀ k, k ≤ c.tolerance →
      k < a.tolerance → a.threshold (k+1) ≤ c.threshold k →
      r (3+k)=0 ∧ (k=0 → r 6=0) ∧ (k=1 → r 7=0))
    (hpositive : ∀ k, k ≤ c.tolerance → r k≠0 →
      c.guard ≠ (if k=0 then a.threshold k else min (a.threshold k) (c.threshold (k-1)))) :
    recordAllowedFor caps a c r = true := by sorry
