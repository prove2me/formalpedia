-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_isFinite_flat_and_finrank_basisDivisor_eq_finrank_torsionIdeal
-- name    : WeierstrassCurve.DrinfeldGlobal.isFinite_flat_and_finrank_basisDivisor_eq_finrank_torsionIdeal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/92ee7fd4-73ae-524b-b4e5-41c3c2b124c2
-- title:
--   Equal ranks of E[q] and the Drinfeld divisor
-- statement:
--   Let $T$ be a commutative ring and $W$ a Weierstrass curve over $T$ which is elliptic; write $E \to \operatorname{Spec} T$ for the structure morphism `projModelStrCR W` of the projective model, obtained from $\operatorname{Proj}$ of the graded quotient ring of the Weierstrass cubic. Let $G$ be a relative group law on this morphism, i.e. functorially compatible unit, multiplication and inverse on $T$-scheme-valued sections satisfying the group axioms. Assume (i) there is a family of bijections $ev$ between sections over $\operatorname{Spec} F$, for $F$ a field extension of $T$, and the points of the affine base change $W_F$, which turns the group law into addition of points and intertwines Galois twisting with the induced map on points; and (ii) there is a ring homomorphism $\chi$ from the origin chart ring (the degree-zero localisation away from the coordinate $y$) to $T$ which presents the unit section $G.one$ as $\operatorname{Spec}\chi$ followed by the origin chart immersion and kills $x/y$ and $z/y$. Let $q$ be a prime and $P, Q$ two sections. Consider two quasi-coherent ideal sheaf data on the pullback of $E \to \operatorname{Spec} T$ along the identity of $\operatorname{Spec} T$: `torsionIdeal G q`, the kernel ideal of the first projection of the pullback of the multiplication-by-$q$ morphism `G.schemeNsmul q` against the unit section, composed with the canonical map `toPullbackId`; and `basisDivisor G q P Q`, the product over $i \in \operatorname{Fin}(q\cdot q)$ of the kernel ideals of the graphs of the sections $\lfloor i/q\rfloor P + (i \bmod q) Q$. The assertion is that the closed immersion cut out by `torsionIdeal G q` followed by the second projection to $\operatorname{Spec} T$ is finite, flat and locally of finite presentation; that the corresponding morphism for `basisDivisor G q P Q` is flat and locally of finite presentation; and that at every point $s$ of $\operatorname{Spec} T$ the two morphisms have the same `finrank`.
--
--   This is the comparison, in the style of Katz–Mazur's treatment of Drinfeld level structures, between the $q$-torsion subscheme $E[q]$ and the divisor $\sum_{0 \le a,b < q} [aP + bQ]$ attached to a pair of sections: both are flat over the base of the same rank (namely $q^2$), so that the divisor can be compared with $E[q]$ fibrewise. It feeds the characterisation of Drinfeld bases in terms of $q$-torsion and the factorisation of the $q$-division series.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_isFinite_flat_and_finrank_basisDivisor_eq_finrank_torsionIdeal.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSum
import Definitions.Def_WeierstrassCurve_SectionAtOrigin

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel
  WeierstrassCurve.DrinfeldGlobal

attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.isFinite_flat_and_finrank_basisDivisor_eq_finrank_torsionIdeal
    {T : Type} [CommRing T] (W : WeierstrassCurve T) [W.IsElliptic]
    (G : RelativeGroupLaw T (projModelStrCR W)) (hG : ∃ ev, IsPointsEval W G ev)
    (hGO : ∃ χ : OriginChartRing W →+* T,
      IsOriginChartSection (G.one (𝟙 _)) χ ∧ χ (xOverY W) = 0 ∧ χ (zOverY W) = 0)
    (q : ℕ) [Fact q.Prime] (P Q : Section W) :
    IsFinite ((torsionIdeal G q).subschemeι ≫ pullback.snd (projModelStrCR W) (𝟙 (base (T := T)))) ∧
    Flat ((torsionIdeal G q).subschemeι ≫ pullback.snd (projModelStrCR W) (𝟙 (base (T := T)))) ∧
    LocallyOfFinitePresentation ((torsionIdeal G q).subschemeι ≫ pullback.snd (projModelStrCR W) (𝟙 (base (T := T)))) ∧
    Flat ((basisDivisor G q P Q).subschemeι ≫ pullback.snd (projModelStrCR W) (𝟙 (base (T := T)))) ∧
    LocallyOfFinitePresentation ((basisDivisor G q P Q).subschemeι ≫ pullback.snd (projModelStrCR W) (𝟙 (base (T := T)))) ∧
    ∀ s, ((basisDivisor G q P Q).subschemeι ≫ pullback.snd (projModelStrCR W) (𝟙 (base (T := T)))).finrank s =
      ((torsionIdeal G q).subschemeι ≫ pullback.snd (projModelStrCR W) (𝟙 (base (T := T)))).finrank s := by sorry
