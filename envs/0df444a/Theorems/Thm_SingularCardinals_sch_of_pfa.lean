-- Prove2me | Theorems.Thm_SingularCardinals_sch_of_pfa
-- name    : SingularCardinals.sch_of_pfa
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-11T14:53:15.769298+00:00
-- url     : https://prove2.me/theorems/afcd6949-edcc-4b7f-b26c-16fecbd8be39
-- title:
--   PFA implies SCH
-- statement:
--   Assume the proper forcing axiom (PFA). Then the singular cardinals hypothesis holds: for every singular strong limit cardinal $\kappa$,
--   $$2^\kappa=\kappa^+.$$
--
--   Since PFA refutes GCH, this shows SCH follows from hypotheses of a very different kind than GCH.
-- source:
--   Wikipedia, "Singular cardinals hypothesis", revision oldid=1349753131, https://en.wikipedia.org/w/index.php?title=Singular_cardinals_hypothesis&oldid=1349753131, last paragraph: "the proper forcing axiom ... also implies SCH".

import Mathlib
import Definitions.Def_JechStationary
import Definitions.Def_SingularCardinals_basic
import Definitions.Def_SingularCardinals_PFA

universe u

open Cardinal

namespace SingularCardinals

theorem sch_of_pfa (h : PFA.{u}) : SCH.{u} := by sorry

end SingularCardinals
