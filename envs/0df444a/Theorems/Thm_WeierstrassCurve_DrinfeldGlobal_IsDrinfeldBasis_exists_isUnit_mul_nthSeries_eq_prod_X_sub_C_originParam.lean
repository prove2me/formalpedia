-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_IsDrinfeldBasis_exists_isUnit_mul_nthSeries_eq_prod_X_sub_C_originParam
-- name    : WeierstrassCurve.DrinfeldGlobal.IsDrinfeldBasis.exists_isUnit_mul_nthSeries_eq_prod_X_sub_C_originParam
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/97e79b91-74c3-5040-ae5b-10b2c634c1ae
-- title:
--   Drinfeld basis factorisation of the q-division series
-- statement:
--   Let $T$ be a Noetherian local commutative ring that is complete (and separated) for the adic topology of its maximal ideal, let $W$ be a Weierstrass curve over $T$ which is elliptic, and let $F$ be a formal group over $T$ whose underlying two-variable power series is the fixed formal group law $W.\mathrm{formalGroupLawFixed}$ of $W$. Let $G$ be a relative group law on the projective model $\mathrm{projModelStrCR}\,W \to \operatorname{Spec} T$, that is, a functorial group structure on sections over varying base schemes, and assume: (i) there is an evaluation family $ev$ identifying sections over $\operatorname{Spec} F$, for $F$ a field over $T$, with affine points of the base change, under which $G$'s multiplication becomes addition of points and which is equivariant for $T$-algebra automorphisms; (ii) the unit section $G.\mathrm{one}(\mathbf 1)$ is the origin-chart section attached to some ring homomorphism $\chi : \mathrm{OriginChartRing}\,W \to T$ with $\chi(x/y) = \chi(z/y) = 0$. Let $q$ be prime and let $P, Q$ be sections with $\mathrm{basisDivisor}\,G\,q\,P\,Q = \mathrm{torsionIdeal}\,G\,q$. Let $S \subseteq \{0,\dots,q-1\}^2$ be a finite set and $\chi : \mathbb N \times \mathbb N \to (\mathrm{OriginChartRing}\,W \to T)$ a family of ring homomorphisms such that for $(a,b) \in S$ the section $\mathrm{linComb}\,G\,P\,Q\,a\,b = [a]P +_G [b]Q$ reduces to the origin along $\chi(a,b)$, i.e. it is the origin-chart section of $\chi(a,b)$ and both $\mathrm{originParam}(\chi(a,b)) = -\chi(a,b)(x/y)$ and $\mathrm{originW}(\chi(a,b))$ lie in the maximal ideal, while for $(a,b)$ in $\{0,\dots,q-1\}^2 \setminus S$ no ring homomorphism makes $[a]P +_G [b]Q$ reduce to the origin. Then there is a unit $u \in T[\![X]\!]$ with $$u \cdot F.\mathrm{nthSeries}\,q = \prod_{(a,b) \in S}\bigl(X - \mathrm{originParam}(\chi(a,b))\bigr),$$ where $\mathrm{nthSeries}$ is defined by $\mathrm{nthSeries}\,0 = 0$ and $\mathrm{nthSeries}(n+1) = F(\mathrm{nthSeries}\,n, X)$, so that $\mathrm{nthSeries}\,q$ is the multiplication-by-$q$ series of $F$.
--
--   This is the local form of the divisor-at-the-origin statement of Katz–Mazur: for a global Drinfeld basis of level $q$, the $q$-division series of the formal group is, up to a unit of $T[\![X]\!]$, the product of $X - z(R)$ over those points $R = [a]P + [b]Q$ whose reduction is the origin. It feeds the counting of such points, the comparison with $[q]_F$ being a unit times a power of $X$, and the adic characterisation of Drinfeld bases.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_IsDrinfeldBasis_exists_isUnit_mul_nthSeries_eq_prod_X_sub_C_originParam.lean

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_FormalGroup
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal IsLocalRing

attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.IsDrinfeldBasis.exists_isUnit_mul_nthSeries_eq_prod_X_sub_C_originParam
    {T : Type} [CommRing T] [IsLocalRing T] [IsNoetherianRing T] [IsAdicComplete (maximalIdeal T) T]
    (W : WeierstrassCurve T) [W.IsElliptic]
    (F : FormalGroup T) (hFW : F.toPowerSeries = W.formalGroupLawFixed)
    (G : RelativeGroupLaw T (projModelStrCR W))
    (hGpts : ∃ ev, IsPointsEval W G ev)
    (hGone : ∃ χ : OriginChartRing W →+* T,
      IsOriginChartSection (G.one (𝟙 _)) χ ∧ χ (xOverY W) = 0 ∧ χ (zOverY W) = 0)
    (q : ℕ) [Fact q.Prime]
    (P Q : Section W) (hPQ : IsDrinfeldBasis G q P Q)
    (S : Finset (ℕ × ℕ)) (hS : S ⊆ Finset.range q ×ˢ Finset.range q)
    (χ : ℕ × ℕ → (OriginChartRing W →+* T))
    (hχ : ∀ ab ∈ S, ReducesToOrigin (linComb G P Q ab.1 ab.2) (χ ab) (maximalIdeal T))
    (hnS : ∀ ab ∈ Finset.range q ×ˢ Finset.range q, ab ∉ S →
      ∀ χ' : OriginChartRing W →+* T, ¬ ReducesToOrigin (linComb G P Q ab.1 ab.2) χ' (maximalIdeal T)) :
    ∃ u : PowerSeries T, IsUnit u ∧
      u * F.nthSeries q = ∏ ab ∈ S, (PowerSeries.X - PowerSeries.C (originParam (χ ab))) := by sorry
