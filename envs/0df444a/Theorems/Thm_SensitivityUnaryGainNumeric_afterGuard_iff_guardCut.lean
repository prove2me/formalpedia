-- Prove2me | Theorems.Thm_SensitivityUnaryGainNumeric_afterGuard_iff_guardCut
-- name    : SensitivityUnaryGainNumeric.afterGuard_iff_guardCut
-- status  : Open
-- author  : @yousofy
-- created : 2026-11-24T16:02:37.899804+00:00
-- url     : https://prove2.me/theorems/1c262186-1acf-4ff1-84fc-fafe7a4e9570
-- title:
--   Accepted replacement guard heights form an initial interval
-- statement:
--   Fix a numerical unary state and rank $j$. Suppose the soft cutoff is at most the hard cutoff and the target is monotone in the allowed failure count. For every replacement height $h'\le12$,
--   $$
--   \operatorname{afterGuard}(j,h')
--   \iff \operatorname{guardBase}(j)\ \land\
--   h'\le\operatorname{guardCut}(j).
--   $$
--   The base predicate removes the selected guard's old occupancy. The cutoff is the minimum of $12$, the hard cutoff, and the soft cutoff when adding one soft failure is not accepted.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/UnaryGainFast.lean lines 38–75; SHA256 428f440faee9336a86c07994867c663c320f717a9edfebdff23cf74cc11d15e6; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

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

theorem SensitivityUnaryGainNumeric.afterGuard_iff_guardCut (r : Recipe) (j : Fin 12) (s : State) (old fresh : ℕ)
    (hmono : GuardMonotone r j) (hfresh : fresh ≤ 12) :
    afterGuard r j s old fresh ↔ guardBase r j s old ∧ fresh ≤ guardCut r j s old := by sorry
