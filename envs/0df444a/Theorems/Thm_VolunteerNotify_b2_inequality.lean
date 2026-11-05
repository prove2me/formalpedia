-- Prove2me | Theorems.Thm_VolunteerNotify_b2_inequality
-- name    : VolunteerNotify.b2_inequality
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:38:50.886262+00:00
-- url     : https://prove2.me/theorems/7d366747-a015-4f6c-b0ca-dc1ff7adaac2
-- title:
--   Appendix B.2, p.36 — $1-\prod_v(1-x_{v,s,t}p_{v,s})\ge(1-\frac1e)\min\{\sum_v x_{v,s,t}p_{v,s},1\}$
-- statement:
--   For any $x\in\mathcal P$, task type $s$ and time $t$,
--   $$
--   1-\prod_{v=1}^V(1-x_{v,s,t}p_{v,s})\ge\Bigl(1-\frac1e\Bigr)\min\Bigl\{\sum_{v=1}^V x_{v,s,t}p_{v,s},\,1\Bigr\}.
--   $$
--   Summing this over $s$ and $t$ with weights $\lambda_{s,t}$ compares $f$ with the objective of (LP).
--
--   **Formalization Note** As on the page, there is no assumption that $\sum_v x_{v,s,t}p_{v,s}\le1$.
--
--   Differences from the source:
--   - encoding: indices in [a] = {1, …, a} → `Fin a`, paper index = value + 1, a = 0 allowed; reason: Lean convention; at a = 0 the sums are empty and no instance of the source changes
--   - encoding: Z > 0 with law g, τ ∈ ℕ → `g : ℕ → ℝ` with `g 0 = 0`, τ ranges over positive integers; reason: ℕ is {1, 2, …} in the source; same instances
-- source:
--   Manshadi, Rodilitz, Online Policies for Efficient Volunteer Crowdsourcing, arXiv:2002.08474v7, Appendix B.2, p.36

import Mathlib
import Definitions.Def_VolunteerNotify_lpValue

namespace VolunteerNotify

/-- The inequality opening Appendix B.2, Manshadi–Rodilitz, arXiv:2002.08474v7, p.36: for any
`x ∈ P`, type `s` and time `t`,
`1 − ∏_v (1 − x_{v,s,t} p_{v,s}) ≥ (1 − 1/e) min{∑_v x_{v,s,t} p_{v,s}, 1}`.

**Formalization Note.** As on the page, `∑_v x_{v,s,t} p_{v,s}` is not capped at `1`. -/
theorem b2_inequality {V S T : ℕ} (I : Instance V S T) (x : Decision V S T)
    (hx : x ∈ feasibleSet I) (s : Fin S) (t : Fin T) :
    (1 - 1 / Real.exp 1) * min (∑ v, x v s t * I.p v s) 1 ≤
      1 - ∏ v, (1 - x v s t * I.p v s) := by sorry

end VolunteerNotify
