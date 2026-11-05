-- Prove2me | Theorems.Thm_VolunteerNotify_claim_2
-- name    : VolunteerNotify.claim_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:36:53.777216+00:00
-- url     : https://prove2.me/theorems/e714fc28-68b9-45cc-bb32-ebdf87ac83b0
-- title:
--   Claim 2 — $\frac{1-(1-c/n)^n}{c}>1-\frac1e$
-- statement:
--   For any integer $n\ge1$ and $c\in(0,1]$,
--   $$
--   \frac{1-(1-c/n)^n}{c}>1-\frac1e.
--   $$
--   Combined with Claim 1, this gives the offline loss $1-1/e$ of the ex ante solution.
--
--   **Formalization Note** The printed domain $c\in[0,1]$ contains $c=0$, where the fraction is $0/0$ and so undefined; that point is excluded.
--
--   Differences from the source:
--   - encoding: c ∈ [0, 1] → c ∈ (0, 1]; reason: at c = 0 the fraction is the undefined 0/0, a nondegeneracy condition only; Lean's value 0 there would make the claim false
--   - encoding: n ∈ ℕ → `n : ℕ` with `1 ≤ n`; reason: ℕ is {1, 2, …} in the source
-- source:
--   Manshadi, Rodilitz, Online Policies for Efficient Volunteer Crowdsourcing, arXiv:2002.08474v7, Claim 2, p.36

import Mathlib

namespace VolunteerNotify

/-- Claim 2, Manshadi–Rodilitz, arXiv:2002.08474v7, p.36: for `n ≥ 1` and `c ∈ (0, 1]`,
`(1 − (1 − c/n)ⁿ)/c > 1 − 1/e`.

**Formalization Note.** The printed `c ∈ [0, 1]` includes `c = 0`, where the fraction is `0/0`;
the fraction is undefined there, so `c = 0` is excluded. -/
theorem claim_2 (n : ℕ) (hn : 1 ≤ n) (c : ℝ) (hc : c ∈ Set.Ioc (0 : ℝ) 1) :
    1 - 1 / Real.exp 1 < (1 - (1 - c / n) ^ n) / c := by sorry

end VolunteerNotify
