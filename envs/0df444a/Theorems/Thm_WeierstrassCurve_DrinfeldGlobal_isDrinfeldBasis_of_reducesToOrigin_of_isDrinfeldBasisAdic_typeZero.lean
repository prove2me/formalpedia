-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_isDrinfeldBasis_of_reducesToOrigin_of_isDrinfeldBasisAdic_typeZero
-- name    : WeierstrassCurve.DrinfeldGlobal.isDrinfeldBasis_of_reducesToOrigin_of_isDrinfeldBasisAdic_typeZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/9901190a-aa0c-50f6-a8b0-82be18e2957f
-- title:
--   Formal Drinfeld basis gives a global Drinfeld Γ(q)-basis
-- statement:
--   Let $T$ be a Noetherian local ring which is complete for the $\mathfrak m$-adic topology, $\mathfrak m =$ `maximalIdeal T`, and let $W$ be a Weierstrass curve over $T$ whose discriminant $W.\Delta$ is a unit. Let $F$ be a formal group over $T$ whose underlying two-variable power series is the fixed Weierstrass formal group law `W.formalGroupLawFixed`, and let $G$ be a relative group law on the structure morphism `projModelStrCR W` from the graded Proj model of $W$ to $\operatorname{Spec} T$, i.e. a functorial group structure on $T$-sections of that model. Assume (i) $G$ admits a points-evaluation: a family of bijections, for every field $F$ with a $T$-algebra structure, between sections over $\operatorname{Spec} F$ and the affine points of $W_F$, carrying `G.mul` to addition of points and commuting with Galois twists; (ii) the unit section $G.\mathrm{one}(\mathbb 1)$ is cut out by a ring homomorphism $\chi$ from the origin chart ring `OriginChartRing W` to $T$ with $\chi(\mathrm{xOverY}) = \chi(\mathrm{zOverY}) = 0$. Let $q$ be a prime, and let $P, Q$ be sections of the Proj model over the identity of the base, each factoring through the origin chart via ring homomorphisms $\chi_P, \chi_Q \colon \mathrm{OriginChartRing}\,W \to T$ with $\mathrm{originParam}\,\chi = -\chi(\mathrm{xOverY})$ and $\mathrm{originW}\,\chi$ both in $\mathfrak m$. Assume finally that the pair of parameters $(\mathrm{originParam}\,\chi_P, \mathrm{originParam}\,\chi_Q)$ is a Drinfeld basis of level $q$ for $F$ in the $\mathfrak m$-adic sense: $F.\mathrm{nthSeries}\,q$ equals a unit power series times $\prod_{a,b<q}\bigl(X - C(F.\mathrm{linComb}\,x_0\,x_1\,a\,b)\bigr)$, the linear combinations being formed for the $\mathfrak m$-adic topology. Then $(P,Q)$ is a Drinfeld basis for $G$ of level $q$, that is, $\mathrm{basisDivisor}\,G\,q\,P\,Q = \mathrm{torsionIdeal}\,G\,q$. Primality of $q$ enters only through $q > 0$.
--
--   This is the converse direction of the comparison between formal and global Drinfeld level structures (Katz–Mazur §5.5): a Drinfeld basis of the formal group attached to $W$, given by the origin-chart parameters of two sections, is already a Drinfeld $\Gamma(q)$-basis of the elliptic curve over the complete local base. It is used in the construction of level structures on completed stalks of modular curves, where the local data of the moduli package is transported to a deformation ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_isDrinfeldBasis_of_reducesToOrigin_of_isDrinfeldBasisAdic_typeZero.lean

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
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

theorem WeierstrassCurve.DrinfeldGlobal.isDrinfeldBasis_of_reducesToOrigin_of_isDrinfeldBasisAdic_typeZero
    {T : Type} [CommRing T] [IsLocalRing T] [IsNoetherianRing T] [IsAdicComplete (maximalIdeal T) T]
    (W : WeierstrassCurve T) (hΔ : IsUnit W.Δ)
    (F : FormalGroup T) (hFW : F.toPowerSeries = W.formalGroupLawFixed)
    (G : RelativeGroupLaw T (projModelStrCR W))
    (hGpts : ∃ ev, IsPointsEval W G ev)
    (hGone : ∃ χ : OriginChartRing W →+* T,
      IsOriginChartSection (G.one (𝟙 _)) χ ∧ χ (xOverY W) = 0 ∧ χ (zOverY W) = 0)
    (q : ℕ) [Fact q.Prime]
    (P Q : Section W) (χP χQ : OriginChartRing W →+* T)
    (hP : ReducesToOrigin P χP (maximalIdeal T)) (hQ : ReducesToOrigin Q χQ (maximalIdeal T))
    (hD : F.IsDrinfeldBasisAdic (maximalIdeal T) q (originParam χP) (originParam χQ)) :
    IsDrinfeldBasis G q P Q := by sorry
