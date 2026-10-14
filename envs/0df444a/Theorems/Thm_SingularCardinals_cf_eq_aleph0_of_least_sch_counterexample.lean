-- Prove2me | Theorems.Thm_SingularCardinals_cf_eq_aleph0_of_least_sch_counterexample
-- name    : SingularCardinals.cf_eq_aleph0_of_least_sch_counterexample
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-11T14:49:32.833615+00:00
-- url     : https://prove2.me/theorems/793ae607-7e15-4204-815d-ec20e7ad7524
-- title:
--   The least counterexample to SCH has countable cofinality
-- statement:
--   Let $\kappa$ be the least counterexample to the singular cardinals hypothesis: $\kappa$ is a singular strong limit cardinal with $2^\kappa\neq\kappa^+$, and every singular strong limit cardinal $\mu<\kappa$ satisfies $2^\mu=\mu^+$. Then
--   $$\operatorname{cf}\kappa=\aleph_0.$$
--
--   This is the "in particular" consequence of Silver's theorem recorded in the source.
-- source:
--   Wikipedia, "Singular cardinals hypothesis", revision oldid=1349753131, https://en.wikipedia.org/w/index.php?title=Singular_cardinals_hypothesis&oldid=1349753131, paragraph beginning "Jack Silver proved ...": "In particular, then, if κ is the least counterexample to the singular cardinals hypothesis, then cf(κ) = ℵ₀."

import Mathlib
import Definitions.Def_JechStationary
import Definitions.Def_SingularCardinals_basic

universe u

open Cardinal

namespace SingularCardinals

theorem cf_eq_aleph0_of_least_sch_counterexample (κ : Cardinal.{u})
    (hsing : κ.IsSingular) (hlim : IsStrongLimit κ) (hfail : 2 ^ κ ≠ Order.succ κ)
    (hleast : ∀ μ : Cardinal.{u}, μ < κ → μ.IsSingular → IsStrongLimit μ →
      2 ^ μ = Order.succ μ) :
    κ.ord.cof = ℵ₀ := by sorry

end SingularCardinals
