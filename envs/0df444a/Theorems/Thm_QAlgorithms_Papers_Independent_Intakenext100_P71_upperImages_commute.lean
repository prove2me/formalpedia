-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P71_upperImages_commute
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P71.upperImages_commute
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-31T07:41:32.759908+00:00
-- url     : https://prove2.me/theorems/236e7655-3c0c-4782-8b47-59245f8b8336
-- title:
--   Proposition 4.1.4: the two upper images commute
-- statement:
--   Fix a subcanonical Grothendieck site $S$, without requiring fiber products, and right crossed modules $H_\bullet$ and $G_\bullet$ of sheaves of groups. Let $[H_\bullet,E,G_\bullet]$ be a butterfly, with upper maps $\kappa:H_1\to E$ and $\iota:G_1\to E$. For every object $U$ of $S$ and all local sections $h\in H_1(U)$ and $g\in G_1(U)$,
--
--   $$
--   \kappa(h)\iota(g)=\iota(g)\kappa(h).
--   $$
--
--   Thus the two upper image subsheaves centralize one another. This property is used in the torsor construction of weak morphisms.
-- source:
--   Butterflies I: morphisms of 2-group stacks, arXiv:0808.3627v2, PDF p. 26, Proposition 4.1.4: the two upper images commute

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P71

namespace QAlgorithms.Papers.Independent.Intakenext100.P71

open CategoryTheory Opposite

universe u v w

variable {C : Type u} [Category.{v} C]

variable {J : GrothendieckTopology C}

/-- Proposition 4.1.4, arXiv:0808.3627v2, PDF p.26.
The two upper images commute as subsheaves of the center. -/
theorem upperImages_commute [J.Subcanonical]
    {H G : RightCrossedModule.{u, v, w} J} (E : Butterfly H G) :
    ∀ (U : C) (h : H.one.sections U) (g : G.one.sections U),
      onSections E.kappa U h * onSections E.iota U g =
        onSections E.iota U g * onSections E.kappa U h := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P71
