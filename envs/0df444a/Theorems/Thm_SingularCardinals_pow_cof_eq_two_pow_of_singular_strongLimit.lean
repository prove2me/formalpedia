-- Prove2me | Theorems.Thm_SingularCardinals_pow_cof_eq_two_pow_of_singular_strongLimit
-- name    : SingularCardinals.pow_cof_eq_two_pow_of_singular_strongLimit
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-11T14:48:36.648882+00:00
-- url     : https://prove2.me/theorems/614f009d-9445-4ceb-84e0-847a9b3839c6
-- title:
--   For singular strong limit κ, κ^{cf κ} = 2^κ
-- statement:
--   Let $\kappa$ be a singular strong limit cardinal, with cofinality $\operatorname{cf}\kappa<\kappa$. Then
--   $$\kappa^{\operatorname{cf}\kappa}=2^\kappa.$$
--
--   This identity links the two forms of SCH: at a singular strong limit cardinal, the second form's conclusion $\kappa^{\operatorname{cf}\kappa}=\kappa^+$ is exactly the first form's $2^\kappa=\kappa^+$.
-- source:
--   Wikipedia, "Singular cardinals hypothesis", revision oldid=1349753131, https://en.wikipedia.org/w/index.php?title=Singular_cardinals_hypothesis&oldid=1349753131, paragraph "Another form of the SCH": "Note that κ^cf(κ) = 2^κ for all singular strong limit cardinals κ."

import Mathlib
import Definitions.Def_JechStationary
import Definitions.Def_SingularCardinals_basic

universe u

open Cardinal

namespace SingularCardinals

theorem pow_cof_eq_two_pow_of_singular_strongLimit (κ : Cardinal.{u})
    (hsing : κ.IsSingular) (hlim : IsStrongLimit κ) :
    κ ^ κ.ord.cof = 2 ^ κ := by sorry

end SingularCardinals
