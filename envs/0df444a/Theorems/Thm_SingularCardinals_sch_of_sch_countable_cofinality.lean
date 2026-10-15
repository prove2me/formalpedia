-- Prove2me | Theorems.Thm_SingularCardinals_sch_of_sch_countable_cofinality
-- name    : SingularCardinals.sch_of_sch_countable_cofinality
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-11T14:53:49.387+00:00
-- url     : https://prove2.me/theorems/6811b664-eb39-4ed1-b97b-60d376321496
-- title:
--   Silver: if SCH holds at all singular strong limits of countable cofinality, SCH holds
-- statement:
--   Suppose the singular cardinals hypothesis holds at every singular strong limit cardinal of countable cofinality: for every singular strong limit cardinal $\lambda$ with $\operatorname{cf}\lambda=\aleph_0$,
--   $$2^\lambda=\lambda^+.$$
--   Then the singular cardinals hypothesis holds at every singular strong limit cardinal $\kappa$, whatever its cofinality:
--   $$2^\kappa=\kappa^+.$$
--
--   This is the consequence of Silver's theorem singled out in the source: failures of SCH can only first occur at cardinals of countable cofinality, which is why the consistency results for $\neg$SCH (Prikry forcing over a measurable cardinal) produce counterexamples such as $\aleph_\omega$.
--
--   **Formalization Note** SCH is the first (strong-limit) form, `SingularCardinals.SCH`. The analogous reduction for the second form is the published theorem `JechSetTheory.sch_of_sch_cof_aleph0`, included in this mission as a milestone.
-- source:
--   Wikipedia, "Singular cardinals hypothesis", revision oldid=1349753131, https://en.wikipedia.org/w/index.php?title=Singular_cardinals_hypothesis&oldid=1349753131, paragraph beginning "Jack Silver proved ...": "if the singular cardinals hypothesis holds for all singular cardinals of countable cofinality, then it holds for all singular cardinals" (with SCH in the first form of the lead section).

import Mathlib
import Definitions.Def_JechStationary
import Definitions.Def_SingularCardinals_basic

universe u

open Cardinal

namespace SingularCardinals

theorem sch_of_sch_countable_cofinality
    (h : ∀ κ : Cardinal.{u}, κ.IsSingular → κ.ord.cof = ℵ₀ → IsStrongLimit κ →
      2 ^ κ = Order.succ κ) :
    SCH.{u} := by sorry

end SingularCardinals
