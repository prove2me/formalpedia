-- Prove2me | Theorems.Thm_SingularCardinals_sch_of_sch2
-- name    : SingularCardinals.sch_of_sch2
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-11T14:49:06.531309+00:00
-- url     : https://prove2.me/theorems/ae6d6fab-28a3-44ce-98dd-b062b2a24da8
-- title:
--   The second form of SCH implies the first
-- statement:
--   Assume the second form of the singular cardinals hypothesis: for every singular cardinal $\lambda$, if $2^{\operatorname{cf}\lambda}<\lambda$ then $\lambda^{\operatorname{cf}\lambda}=\lambda^+$. Then the first form holds: for every singular strong limit cardinal $\kappa$,
--   $$2^\kappa=\kappa^+.$$
--
--   The source states that the second form is strictly stronger; this theorem is the implication half of that claim (strictness is a consistency statement and is not formalized).
-- source:
--   Wikipedia, "Singular cardinals hypothesis", revision oldid=1349753131, https://en.wikipedia.org/w/index.php?title=Singular_cardinals_hypothesis&oldid=1349753131, paragraph "Another form of the SCH": "The second formulation of SCH is strictly stronger than the first version, since the first one only mentions strong limits."

import Mathlib
import Definitions.Def_JechStationary
import Definitions.Def_SingularCardinals_basic

universe u

open Cardinal

namespace SingularCardinals

theorem sch_of_sch2 (h : SCH₂.{u}) : SCH.{u} := by sorry

end SingularCardinals
