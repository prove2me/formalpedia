-- Prove2me | Theorems.Thm_SpecialRelativity_relativity_of_simultaneity
-- name    : SpecialRelativity.relativity_of_simultaneity
-- status  : Open
-- author  : @LG
-- created : 2026-11-27T01:49:45.744251+00:00
-- url     : https://prove2.me/theorems/6a452f08-6376-4105-8912-521c70ef40f7
-- title:
--   Relativity of simultaneity: the boost desynchronizes simultaneous events
-- statement:
--   **Relativity of simultaneity — the boost breaks it.**
--
--   Let $\beta$ be a boost velocity with $0 < \beta < 1$, and let `boost β` be the standard Lorentz boost along the $x$-axis: $\gamma = 1/\sqrt{1-\beta^2}$ on the $(t,t)$ and $(x,x)$ entries, $-\beta\gamma$ on the $(t,x)$ and $(x,t)$ entries, identity on $y, z$.
--
--   **Conclusion:** a two-fold conjunction —
--   1. the boost is a Lorentz transformation: $(\mathrm{boost}\,\beta)^{T}\,\eta\,(\mathrm{boost}\,\beta) = \eta$;
--   2. it breaks simultaneity: for any two events $e_1, e_2$ that are simultaneous in the unboosted frame ($e_1^0 = e_2^0$), spatially separated by exactly one unit in the direction of motion ($e_1^1 - e_2^1 = 1$) and at the same $y$- and $z$-coordinates, the boosted time coordinates differ:
--
--   $$\big((\mathrm{boost}\,\beta)(e_1 - e_2)\big)^0 \;\neq\; 0 \qquad (\text{in fact} = -\beta\,\gamma\,(e_1^1 - e_2^1) = -\beta\gamma).$$
--
--   In words: "events that appear simultaneous to one observer may not be simultaneous to an observer in motion" — the source's first-listed consequence of the two postulates, here in its sharpest quantitative form.
--
--   **Formalization note.** Part 1 is a direct entrywise computation of the congruence, using $0 < \beta < 1$ to keep $\gamma$ and $1 - \beta^2$ real and positive; part 2 is the entry formula for the boosted time component. The unit spatial separation is a normalization (the statement is linear in the separation); any nonzero separation along $x$ works by scaling.
-- source:
--   Wikipedia, Special relativity, https://en.wikipedia.org/wiki/Special_relativity (source of the quoted statements, reproduced verbatim in the definition file) (consequences of the postulates: 'The relativity of simultaneity - events that appear simultaneous to one observer may not be simultaneous to an observer in motion'); A. Einstein, Zur Elektrodynamik bewegter Koerper (1905), Section 2

import Mathlib
import Definitions.Def_SpecialRelativity

namespace SpecialRelativity

open Matrix

/-- Milestone: the relativity of simultaneity.  The standard boost along the
`x`-axis with velocity `β` (`0 < β < 1`) is a Lorentz transformation, and it
breaks simultaneity: two events that are simultaneous (`e₁ 0 = e₂ 0`), spatially
separated by one unit in the direction of motion (`e₁ 1 - e₂ 1 = 1`) and at the
same `y`- and `z`-coordinates in the unboosted frame have **different** time
coordinates in the boosted frame — the boosted time separation is
`-β γ (e₁ 1 - e₂ 1) ≠ 0` with `γ = 1/√(1-β²)`.  "Events that appear simultaneous
to one observer may not be simultaneous to an observer in motion." -/
theorem relativity_of_simultaneity (β : ℝ) (hβ : 0 < β) (hβ1 : β < 1) :
    IsLorentz (boost β) ∧
    ∀ e₁ e₂ : Sp, e₁ 0 = e₂ 0 → e₁ 1 - e₂ 1 = 1 → e₁ 2 = e₂ 2 → e₁ 3 = e₂ 3 →
      ((boost β).mulVec (e₁ - e₂)) 0 ≠ 0 := by
  sorry

end SpecialRelativity
