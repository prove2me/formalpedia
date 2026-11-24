-- Prove2me | Theorems.Thm_SensitivityUnaryOrdinaryGlobalNumeric_mem_states
-- name    : SensitivityUnaryOrdinaryGlobalNumeric.mem_states
-- status  : Open
-- author  : @yousofy
-- created : 2026-11-24T16:02:43.963045+00:00
-- url     : https://prove2.me/theorems/5adcc9c4-facb-437c-918b-3758ed4aa60a
-- title:
--   Completeness of the ordinary unary population enumeration
-- statement:
--   Fix an allowance $q$, a Boolean guard-enable flag, and a population state $(t,g,e)$. If
--   $$
--   t\le2q+1,\qquad g\le2q+3,\qquad
--   e\le g(q+1)-\binom g2,
--   $$
--   and a disabled guard flag implies $g=0$, then this state belongs to the finite ordinary-state list for $q$ and that flag.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/UnaryOrdinaryGlobalNumeric.lean lines 53–67; SHA256 7744d0cc81374ec649af5ddf0b96765ab9ea2b5a2143c050b42d064a46f2fcec; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_Solutions_UnaryOrdinaryGlobalNumeric
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.List.Range
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic

namespace SensitivityLocalNumeric
end SensitivityLocalNumeric
namespace SensitivityUnaryOrdinaryGlobalNumeric
end SensitivityUnaryOrdinaryGlobalNumeric


/-! A direct finite certificate for ordinary unary global gains.  The states
record target heads, guard heads, and distinct donors outside those heads. -/
open SensitivityUnaryOrdinaryGlobalNumeric
open SensitivityLocalNumeric

theorem SensitivityUnaryOrdinaryGlobalNumeric.mem_states (q : ℕ) (enabled : Bool) (s : State)
    (ht : s.targets ≤ 2*q+1) (hg : s.guards ≤ 2*q+3)
    (hdisabled : enabled = false → s.guards = 0)
    (he : s.external ≤ outside q s) : s ∈ states q enabled := by sorry
