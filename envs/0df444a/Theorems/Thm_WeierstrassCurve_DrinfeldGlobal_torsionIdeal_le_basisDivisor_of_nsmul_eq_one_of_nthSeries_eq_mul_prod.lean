-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_torsionIdeal_le_basisDivisor_of_nsmul_eq_one_of_nthSeries_eq_mul_prod
-- name    : WeierstrassCurve.DrinfeldGlobal.torsionIdeal_le_basisDivisor_of_nsmul_eq_one_of_nthSeries_eq_mul_prod
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/c8381951-567f-540f-b220-c4839dbd8e23
-- title:
--   Origin-coset inclusion: basis divisor lies inside E[q]
-- statement:
--   Let $T$ be a Noetherian local ring, complete for the adic topology of its maximal ideal $\mathfrak m_T$, and let $q$ be a prime with $q \in \mathfrak m_T$. Let $W$ be a Weierstrass curve over $T$ with invertible discriminant, let `projModelStrCR W` be its projective model over $\operatorname{Spec} T$, and let $G$ be a relative group law on that model, that is, a functorial group structure on sections over arbitrary $T$-schemes. Assume: $G$ admits a points evaluation, namely a family of bijections, for every field $F$ with a $T$-algebra structure, between $F$-points of the model and points of the affine base change $W_F$, additive for $G$ and equivariant for $T$-automorphisms of $F$; the unit section $G.one(\mathbb{1})$ factors through the origin chart by a ring map $\chi$ with $\chi(x/y) = \chi(z/y) = 0$; $F$ is a formal group over $T$ whose series is $W$'s Weierstrass formal group law `formalGroupLawFixed`; the $q$-th iterate series `F.nthSeries q` $= [q]_F$ reduces, over the residue field, to a unit times $X^q$. Let $P, Q$ be sections over the identity of the base, with $P$ cut out on the origin chart by $\chi_P$ whose origin parameter $-\chi_P(x/y)$ and $-\chi_P(z/y)$ both lie in $\mathfrak m_T$, while $Q$ reduces to the origin through no chart map, and $q$-fold $G$-addition of $Q$ gives the unit section. Assume finally that $[q]_F = u \prod_{a<q}\bigl(X - [a]_F(x_P)\bigr)$ for a unit $u \in T\langle\!\langle X\rangle\!\rangle$, where $[a]_F(x_P)$ denotes the iterated formal sum `F.evalNSMul a` of the origin parameter of $\chi_P$ with itself. Then, as ideal sheaf data on the pullback of the model along the identity of the base, `torsionIdeal G q` — the kernel of the $q$-fold multiplication section composed with `toPullbackId` — is contained in `basisDivisor G q P Q`, the product over $a, b < q$ of the kernel ideals of the graphs of the sections $[a]P + [b]Q$.
--
--   This is the inclusion of the Drinfeld divisor $\sum_{a,b<q}[aP+bQ]$ into the $q$-torsion subscheme $E[q]$, in the ordinary case over a complete Noetherian local base, the notion of Drinfeld basis being as in Katz–Mazur. It supplies the substantive half of the criterion `isDrinfeldBasis_iff_nsmul_eq_one_and_nthSeries_eq_mul_prod_of_reducesToOrigin`, which characterises Drinfeld bases at an ordinary point by $q$-torsion of $Q$ together with the stated factorisation of $[q]_F$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_torsionIdeal_le_basisDivisor_of_nsmul_eq_one_of_nthSeries_eq_mul_prod.lean

import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal IsLocalRing

attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.torsionIdeal_le_basisDivisor_of_nsmul_eq_one_of_nthSeries_eq_mul_prod
    {T : Type} [CommRing T] [IsLocalRing T] [IsNoetherianRing T] [IsAdicComplete (maximalIdeal T) T]
    (q : ℕ) [Fact q.Prime] (hqT : (q : T) ∈ maximalIdeal T)
    (W : WeierstrassCurve T) [W.IsElliptic]
    (G : RelativeGroupLaw T (projModelStrCR W))
    (hG : ∃ ev, IsPointsEval W G ev)
    (hGO : ∃ χ : OriginChartRing W →+* T,
      IsOriginChartSection (G.one (𝟙 _)) χ ∧ χ (xOverY W) = 0 ∧ χ (zOverY W) = 0)
    (F : FormalGroup T) (hFW : F.toPowerSeries = W.formalGroupLawFixed)
    (hord : ∃ u : PowerSeries (ResidueField T), IsUnit u ∧
      PowerSeries.map (residue T) (F.nthSeries q) = u * PowerSeries.X ^ q)
    (P Q : Section W) (χP : OriginChartRing W →+* T) (hP : ReducesToOrigin P χP (maximalIdeal T))
    (hQ : ∀ χ : OriginChartRing W →+* T, ¬ ReducesToOrigin Q χ (maximalIdeal T))
    (hQq : G.nsmul (𝟙 (base (T := T))) q Q = G.one (𝟙 (base (T := T))))
    (hgen : ∃ u : PowerSeries T, IsUnit u ∧
      F.nthSeries q = u * ∏ a ∈ Finset.range q,
        (PowerSeries.X - PowerSeries.C (letI : WithIdeal T := ⟨maximalIdeal T⟩; F.evalNSMul a (originParam χP)))) :
    torsionIdeal G q ≤ basisDivisor G q P Q := by sorry
