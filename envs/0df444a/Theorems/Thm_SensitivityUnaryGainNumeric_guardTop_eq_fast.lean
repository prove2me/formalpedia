-- Prove2me | Theorems.Thm_SensitivityUnaryGainNumeric_guardTop_eq_fast
-- name    : SensitivityUnaryGainNumeric.guardTop_eq_fast
-- status  : Open
-- author  : @yousofy
-- created : 2026-11-24T16:02:41.732128+00:00
-- url     : https://prove2.me/theorems/12a4d2da-f078-477d-8974-185dfe4171a8
-- title:
--   The maximum jointly accepted guard height is the smaller cutoff
-- statement:
--   Assume the guard-monotonicity conditions at two ranks $i,j$, and assume both base states are accepted after removing the selected guard. Then the maximum replacement height accepted at both ranks is
--   $$
--   \operatorname{guardTop}(i,j)
--   =\min\{\operatorname{guardCut}(i),\operatorname{guardCut}(j)\}.
--   $$
--   This is the exact value denoted by $\operatorname{guardTopFast}$.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/UnaryGainFast.lean lines 105–122; SHA256 428f440faee9336a86c07994867c663c320f717a9edfebdff23cf74cc11d15e6; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_Solutions_UnaryGainFast
import Definitions.Def_Sensitivity214439_Phase0_Solutions_UnaryGainNumeric
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.List.Range

namespace SensitivityUnaryGainNumeric
end SensitivityUnaryGainNumeric


/-!
The accepted new guard heights form an initial interval.  Computing its two
threshold endpoints avoids enumerating all thirteen heights inside every
numeric C certificate.  The equality with the exhaustive definition is proved.
-/
open SensitivityUnaryGainNumeric

theorem SensitivityUnaryGainNumeric.guardTop_eq_fast (r : Recipe) (i j : Fin 12) (s : State) (old : ℕ)
    (hi : GuardMonotone r i) (hj : GuardMonotone r j) (hp : guardPossible r i j s old) :
    guardTop r i j s old = guardTopFast r i j s old := by sorry
