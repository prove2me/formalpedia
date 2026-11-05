-- Prove2me | Theorems.Thm_VolunteerNotify_proposition_2
-- name    : VolunteerNotify.proposition_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:39:30.647289+00:00
-- url     : https://prove2.me/theorems/c93b90cf-655a-4d81-bc1b-3577f9dabb30
-- title:
--   Proposition 2 — $f(x^*)\ge(1-\frac1e)\mathrm{LP}$
-- statement:
--   For $x^*$ defined in (5),
--   $$
--   f(x^*)\ge\Bigl(1-\frac1e\Bigr)\mathrm{LP}_{\mathcal I}.
--   $$
--   This is the offline half of the competitive ratio: the ex ante solution loses at most a factor $1-1/e$ against the benchmark.
--
--   Differences from the source:
--   - generalization: x* is the argmax of f over the three candidates of (5) → `IsExAnte`: every value of (5) over any optimizer of (LP), any m ≥ 1 and Frank–Wolfe run, any solution of (SQ-v), and any tie-break; reason: the candidates are not unique; each run of the source is one such value
--   - encoding: indices in [a] = {1, …, a} → `Fin a`, paper index = value + 1, a = 0 allowed; reason: Lean convention; at a = 0 the sums are empty and no instance of the source changes
--   - encoding: LP_I is the maximum of (LP) → `lpValue` is the `sSup` of the objective over P; reason: P is nonempty and compact and the objective is continuous, so the supremum is attained and equals the maximum
--   - encoding: Z > 0 with law g, τ ∈ ℕ → `g : ℕ → ℝ` with `g 0 = 0`, τ ranges over positive integers; reason: ℕ is {1, 2, …} in the source; same instances
-- source:
--   Manshadi, Rodilitz, Online Policies for Efficient Volunteer Crowdsourcing, arXiv:2002.08474v7, Proposition 2, p.15

import Mathlib
import Definitions.Def_VolunteerNotify_IsExAnte

namespace VolunteerNotify

/-- Proposition 2, Manshadi–Rodilitz, arXiv:2002.08474v7, p.15: for `x*` defined in (5),
`f(x*) ≥ (1 − 1/e) LP`. -/
theorem proposition_2 {V S T : ℕ} (I : Instance V S T) (xstar : Decision V S T)
    (hx : IsExAnte I xstar) : (1 - 1 / Real.exp 1) * lpValue I ≤ f I xstar := by sorry

end VolunteerNotify
