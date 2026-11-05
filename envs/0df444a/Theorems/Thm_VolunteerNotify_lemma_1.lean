-- Prove2me | Theorems.Thm_VolunteerNotify_lemma_1
-- name    : VolunteerNotify.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:38:21.949205+00:00
-- url     : https://prove2.me/theorems/b8a75f73-4f8e-4f12-962e-58b170bf7e3b
-- title:
--   Lemma 1 — $f(x)=\sum_v f_v(x)$
-- statement:
--   For any $x\in[0,1]^{V\times S\times T}$,
--   $$
--   f(x)=\sum_{v=1}^V f_v(x),
--   $$
--   where $f$ and $f_v$ are defined in (3) and (4). This is the decomposition of the always-active objective into per-volunteer contributions under the index-based priority scheme.
--
--   Differences from the source:
--   - encoding: indices in [a] = {1, …, a} → `Fin a`, paper index = value + 1, a = 0 allowed; reason: Lean convention; at a = 0 the sums are empty and no instance of the source changes
--   - encoding: Z > 0 with law g, τ ∈ ℕ → `g : ℕ → ℝ` with `g 0 = 0`, τ ranges over positive integers; reason: ℕ is {1, 2, …} in the source; same instances
-- source:
--   Manshadi, Rodilitz, Online Policies for Efficient Volunteer Crowdsourcing, arXiv:2002.08474v7, Lemma 1, p.14

import Mathlib
import Definitions.Def_VolunteerNotify_f

namespace VolunteerNotify

/-- Lemma 1, Manshadi–Rodilitz, arXiv:2002.08474v7, p.14: for any `x ∈ [0,1]^{V×S×T}`,
`f(x) = ∑_v f_v(x)`. -/
theorem lemma_1 {V S T : ℕ} (I : Instance V S T) (x : Decision V S T)
    (hx : ∀ v s t, x v s t ∈ Set.Icc (0 : ℝ) 1) : f I x = ∑ v, fv I x v := by sorry

end VolunteerNotify
