-- Prove2me | Theorems.Thm_SingularCardinals_sch_of_gch
-- name    : SingularCardinals.sch_of_gch
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-11T14:48:12.745973+00:00
-- url     : https://prove2.me/theorems/c8f6583c-632b-4b7a-9ca0-10147cbb405b
-- title:
--   GCH implies SCH
-- statement:
--   If the generalized continuum hypothesis holds, that is $2^\lambda=\lambda^+$ for every infinite cardinal $\lambda$, then the singular cardinals hypothesis holds: for every singular strong limit cardinal $\kappa$,
--   $$2^\kappa=\kappa^+.$$
--
--   Together with the consistency of GCH this is the source's argument that SCH is consistent with ZFC.
-- source:
--   Wikipedia, "Singular cardinals hypothesis", revision oldid=1349753131, https://en.wikipedia.org/w/index.php?title=Singular_cardinals_hypothesis&oldid=1349753131, second paragraph ("Since SCH is a consequence of GCH ...") and last paragraph ("As was noted above, GCH implies SCH").

import Mathlib
import Definitions.Def_JechStationary
import Definitions.Def_SingularCardinals_basic

universe u

open Cardinal

namespace SingularCardinals

theorem sch_of_gch (h : GCH.{u}) : SCH.{u} := by sorry

end SingularCardinals
