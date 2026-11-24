-- Prove2me | Theorems.Thm_SensitivityActiveSocketGeometry_inactive_check_cleanlyDominates
-- name    : SensitivityActiveSocketGeometry.inactive_check_cleanlyDominates
-- status  : Proved
-- author  : @yousofy
-- created : 2026-11-24T20:33:47.629474+00:00
-- url     : https://prove2.me/theorems/254a0ee3-7fc7-484a-93cc-379dd7ce3552
-- title:
--   An inactive incoming check cleanly dominates an active candidate
-- statement:
--   Consider a paired arc $h\to v$ and its guard check. Suppose a selected side $a(v)$ of the destination passes the cutoff, while the check from $h$ is inactive. Then $h$ and $v$ lie in distinct macros, the macro arc points from $h$ to $v$, and its Boolean label differs from $a(v)$. Equivalently, the marker macro cleanly dominates $v$.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; checked task source lean/Solutions/ActiveSocketMacroGeometry.lean lines 265–285; SHA256 745d14738e6e657e3f16e79a0836e3cda18124fa37719ea8d258c13fa013f29e; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_ActiveSocketMacroGeometry
import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_HighHeadGuardBridge
import Definitions.Def_Sensitivity214439_Phase0_Solutions_RankedBooleanConstruction
import Definitions.Def_Sensitivity214439_Phase0_Solutions_SocketGateConstruction
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Ring.Fin
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace SensitivityActiveSocketGeometry
end SensitivityActiveSocketGeometry
namespace SensitivityCyclicTokens
end SensitivityCyclicTokens
namespace SensitivityHighHeadGuardBridge
end SensitivityHighHeadGuardBridge
namespace SensitivityRankedConstruction
end SensitivityRankedConstruction


/-!
Actual selected positive sockets induce the macro conflict graph used in the
population argument. An independent set contains at most one row per macro.
The complement of each selected socket is a coherent token. Every directed
conflict pays for a different actually active guard, including internal OR
checks. Clean domination gives exactly the literal perfect-marker condition.
-/
open SensitivityActiveSocketGeometry
open scoped Classical Fin.CommRing
open SensitivityRankedConstruction SensitivityHighHeadGuardBridge SensitivityCyclicTokens
set_option autoImplicit false
variable {M B I Color : Type} {L n : ℕ}

theorem SensitivityActiveSocketGeometry.inactive_check_cleanlyDominates
    (row : RowFamily I Color L) (macroArc : M → M → Prop)
    (label : M → M → Bool) (internalArc : B → B → Prop)
    (active : M × B → Bool) (cutoff : ℕ)
    (x : (((M × B) × Bool) × I) → Bool)
    {marker v : M × B} (harc : pairedArc macroArc internalArc marker v)
    (hactive : passes row cutoff (socketInput x (v, active v)))
    (hquiet : ¬ guardActive row cutoff x (pairedCheck label marker v)) :
    CleanlyDominates macroArc label active marker.1 v := by sorry
