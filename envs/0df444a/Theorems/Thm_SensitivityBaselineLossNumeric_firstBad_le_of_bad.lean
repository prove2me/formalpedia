-- Prove2me | Theorems.Thm_SensitivityBaselineLossNumeric_firstBad_le_of_bad
-- name    : SensitivityBaselineLossNumeric.firstBad_le_of_bad
-- status  : Open
-- author  : @yousofy
-- created : 2026-11-24T15:48:43.869849+00:00
-- url     : https://prove2.me/theorems/907d5040-4aab-4cdd-be27-3451725b555f
-- title:
--   Minimality of the first rejecting guard height
-- statement:
--   Fix a numerical recipe $r$, rank $i$, state $s$, and old guard height $h$. If a new height $u<13$ makes the numerical row reject, then the first rejecting height found in the range $0,\ldots,12$ satisfies
--   $$
--   \operatorname{firstBad}(r,i,s,h)\le u.
--   $$
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/BaselineLossNumeric.lean lines 64–80; SHA256 0c63cc64f41372ca81ec16e16ee0d34cf05c1d58d3325d9a866df8a4d3a51b1a; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_Solutions_BaselineLossNumeric
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Range

namespace SensitivityBaselineLossNumeric
end SensitivityBaselineLossNumeric


/-! Small computable certificates for every exact-source baseline loss bound.
The five dual coefficients price physical sockets, checks, two exact soft
counts, and the count witnessing rejection at the next rank. -/
open SensitivityBaselineLossNumeric

theorem SensitivityBaselineLossNumeric.firstBad_le_of_bad (r : Recipe) (i : Fin 12) (s : State) (old fresh : ℕ)
    (hfresh : fresh < 13) (hbad : bad r i s old fresh) : firstBad r i s old ≤ fresh := by sorry
