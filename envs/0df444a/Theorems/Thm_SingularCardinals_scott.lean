-- Prove2me | Theorems.Thm_SingularCardinals_scott
-- name    : SingularCardinals.scott
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-11T14:50:06.648999+00:00
-- url     : https://prove2.me/theorems/340106ec-1c14-4ad3-937c-2121979e2ee1
-- title:
--   Scott: GCH on a measure-one set below a measurable κ gives 2^κ = κ⁺
-- statement:
--   Let $\kappa$ be an uncountable cardinal and let $D$ be a normal measure on $\kappa$ (a nonprincipal, $\kappa$-complete, normal ultrafilter concentrating on the ordinals below $\kappa$; so $\kappa$ is measurable). Suppose GCH holds below $\kappa$ on a set of measure one:
--   $$\{\alpha<\kappa:\ 2^{|\alpha|}=|\alpha|^+\}\in D.$$
--   Then
--   $$2^\kappa=\kappa^+.$$
--
--   Contrapositively, violating GCH at a measurable cardinal requires violating it on a measure-one set below; this is the link between $\neg$SCH and GCH failures at measurable cardinals described in the source.
--
--   **Formalization Note** For an ordinal $\alpha$, $|\alpha|$ is its cardinality (`α.card`); the set of cardinals below $\kappa$ has measure one for a normal measure, so this agrees with the source's set of cardinals $\alpha<\kappa$.
-- source:
--   Wikipedia, "Singular cardinals hypothesis", revision oldid=1349753131, https://en.wikipedia.org/w/index.php?title=Singular_cardinals_hypothesis&oldid=1349753131, paragraph beginning "The negation of the singular cardinals hypothesis is intimately related ...": result of Dana Scott.

import Mathlib
import Definitions.Def_SingularCardinals_largeCardinals

universe u

open Cardinal

namespace SingularCardinals

theorem scott (κ : Cardinal.{u}) (hκ : ℵ₀ < κ) (D : Ultrafilter Ordinal.{u})
    (hD : IsNormalMeasure κ D)
    (hgch : {α : Ordinal.{u} | α < κ.ord ∧ 2 ^ α.card = Order.succ α.card} ∈ D) :
    2 ^ κ = Order.succ κ := by sorry

end SingularCardinals
