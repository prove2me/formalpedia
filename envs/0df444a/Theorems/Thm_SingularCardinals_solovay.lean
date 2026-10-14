-- Prove2me | Theorems.Thm_SingularCardinals_solovay
-- name    : SingularCardinals.solovay
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-11T14:50:34.757508+00:00
-- url     : https://prove2.me/theorems/e37da9a8-e919-45d4-8959-8cf68306e30e
-- title:
--   Solovay: SCH holds above a strongly compact cardinal
-- statement:
--   Let $\kappa$ be a strongly compact cardinal. Then the singular cardinals hypothesis holds above $\kappa$: for every singular strong limit cardinal $\mu>\kappa$,
--   $$2^\mu=\mu^+.$$
--
--   This is the source's example of large cardinals "almost" implying SCH.
-- source:
--   Wikipedia, "Singular cardinals hypothesis", revision oldid=1349753131, https://en.wikipedia.org/w/index.php?title=Singular_cardinals_hypothesis&oldid=1349753131, last paragraph: "Solovay showed that large cardinals almost imply SCH—in particular, if κ is strongly compact cardinal, then the SCH holds above κ."

import Mathlib
import Definitions.Def_SingularCardinals_largeCardinals

universe u

open Cardinal

namespace SingularCardinals

theorem solovay (κ : Cardinal.{u}) (hκ : IsStronglyCompact κ) (μ : Cardinal.{u})
    (hμ : κ < μ) (hsing : μ.IsSingular) (hlim : IsStrongLimit μ) :
    2 ^ μ = Order.succ μ := by sorry

end SingularCardinals
