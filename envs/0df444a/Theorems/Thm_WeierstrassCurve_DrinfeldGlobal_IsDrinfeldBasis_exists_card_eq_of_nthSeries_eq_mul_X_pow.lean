-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_IsDrinfeldBasis_exists_card_eq_of_nthSeries_eq_mul_X_pow
-- name    : WeierstrassCurve.DrinfeldGlobal.IsDrinfeldBasis.exists_card_eq_of_nthSeries_eq_mul_X_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/76a4de94-ffda-5aca-ac6f-e5901884c272
-- title:
--   Ordinary case: exactly q combinations of a Drinfeld basis are the origin
-- statement:
--   Let $k$ be a field, $q$ a prime, and $W$ an elliptic Weierstrass curve over $k$; write $\mathrm{base}=\operatorname{Spec} k$, and let a section mean a morphism to the projective model $\mathtt{projModelStrCR}\,W$ over the identity of $\mathrm{base}$. Let $G$ be a relative group law on that model, i.e. functorial unit, multiplication and inversion operations on sections over arbitrary bases satisfying associativity, the unit laws, left inversion and compatibility with base change. Assume: there is a family of bijections $ev$ between sections over field points and affine points of the base-changed curve which is additive for $G$ and equivariant for algebra automorphisms (`IsPointsEval`); the unit section $G.\mathrm{one}$ factors through the origin chart via a ring homomorphism $\chi$ with $\chi(\mathtt{xOverY}\,W)=\chi(\mathtt{zOverY}\,W)=0$; a formal group $F$ over $k$ whose underlying two-variable series is $W.\mathtt{formalGroupLawFixed}$ is given, and its $q$-th iterated series $F.\mathtt{nthSeries}\,q$ (the $q$-fold substitution defining $[q]_F$) equals $u\cdot X^q$ for some unit $u \in k[[X]]$; finally $P,Q$ are sections with $\mathtt{basisDivisor}\,G\,q\,P\,Q = \mathtt{torsionIdeal}\,G\,q$, i.e. the graph-product ideal sheaf data of the $q^2$ sections $[a]P+[b]Q$ coincides with the kernel ideal of multiplication by $q$ against the unit section. Then there is a finite set $S \subseteq \mathbb{N} \times \mathbb{N}$ whose elements are exactly the pairs $(a,b)$ with $a,b<q$ and $G.\mathrm{mul}([a]P,[b]Q) = G.\mathrm{one}$, and $\#S = q$.
--
--   This is the multiplicity computation at the origin for a Drinfeld basis of level $q$ on an ordinary elliptic curve over a field: of the $q^2$ combinations $[a]P+[b]Q$ with $a,b<q$, exactly $q$ equal the origin section, reflecting that the connected part of the $q$-torsion has order $q$ in the ordinary case. It feeds the separation statement [`WeierstrassCurve.DrinfeldGlobal.exists_linComb_eq_one_and_linComb_ne_one_of_isDrinfeldBasis_of_nthSeries_eq_mul_X_pow_of_isOriginChartSection`](thm.html#WeierstrassCurve.DrinfeldGlobal.exists_linComb_eq_one_and_linComb_ne_one_of_isDrinfeldBasis_of_nthSeries_eq_mul_X_pow_of_isOriginChartSection).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_IsDrinfeldBasis_exists_card_eq_of_nthSeries_eq_mul_X_pow.lean

import Mathlib
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

theorem WeierstrassCurve.DrinfeldGlobal.IsDrinfeldBasis.exists_card_eq_of_nthSeries_eq_mul_X_pow
    {k : Type} [Field k] (q : ℕ) [Fact q.Prime]
    (W : WeierstrassCurve k) [W.IsElliptic]
    (G : RelativeGroupLaw k (projModelStrCR W))
    (hG : ∃ ev, IsPointsEval W G ev)
    (hGO : ∃ χ : OriginChartRing W →+* k,
      IsOriginChartSection (G.one (𝟙 (base (T := k)))) χ ∧ χ (xOverY W) = 0 ∧ χ (zOverY W) = 0)
    (F : FormalGroup k) (hFW : F.toPowerSeries = W.formalGroupLawFixed)
    (hord : ∃ u : PowerSeries k, IsUnit u ∧ F.nthSeries q = u * PowerSeries.X ^ q)
    (P Q : Section W) (hPQ : IsDrinfeldBasis G q P Q) :
    ∃ S : Finset (ℕ × ℕ),
      (∀ ab : ℕ × ℕ, ab ∈ S ↔ ab.1 < q ∧ ab.2 < q ∧ linComb G P Q ab.1 ab.2 = G.one (𝟙 (base (T := k)))) ∧
      S.card = q := by sorry
