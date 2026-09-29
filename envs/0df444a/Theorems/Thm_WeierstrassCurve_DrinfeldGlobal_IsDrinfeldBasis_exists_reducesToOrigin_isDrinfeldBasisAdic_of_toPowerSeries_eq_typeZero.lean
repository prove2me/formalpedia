-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_IsDrinfeldBasis_exists_reducesToOrigin_isDrinfeldBasisAdic_of_toPowerSeries_eq_typeZero
-- name    : WeierstrassCurve.DrinfeldGlobal.IsDrinfeldBasis.exists_reducesToOrigin_isDrinfeldBasisAdic_of_toPowerSeries_eq_typeZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/bc0db0b4-33f5-57f2-8f17-0e293dda74c6
-- title:
--   Global Drinfeld q-basis yields formal Drinfeld basis, supersingular case
-- statement:
--   Let $T$ be a Noetherian local ring that is complete with respect to its maximal ideal, and let $W$ be a Weierstrass curve over $T$ with invertible discriminant. Let $F$ be a formal group law over $T$ whose underlying two-variable power series is the Weierstrass formal group law `W.formalGroupLawFixed`. Let $G$ be a relative group law on the projective model $\mathrm{Proj} \to \mathrm{Spec}\,T$ of $W$, assumed to admit an evaluation `ev` identifying its field-valued points with the affine points of the base change, compatibly with addition and with Galois twists, and whose identity section factors through the origin chart by a ring homomorphism killing both $X/Y$ and $Z/Y$. Let $q$ be a prime and assume that the reduction of $W$ to the residue field has formal group satisfying `IsDrinfeldBasisAdic ⊥ q 0 0`, i.e. its $q$-th iterate series is a unit times $\prod_{a,b<q}(X - C(0\oplus 0))$. Finally let $P,Q$ be sections with `IsDrinfeldBasis G q P Q`: the product of the kernel ideal sheaves of the graphs of the $q^2$ combinations $aP+bQ$ equals the kernel ideal of multiplication by $q$. The conclusion asserts the existence of ring homomorphisms $\chi_P,\chi_Q$ from the origin chart ring to $T$ such that $P$ and $Q$ factor through the origin chart via them with $-\chi(X/Y)$ and $-\chi(Z/Y)$ in the maximal ideal, and such that $F.\mathrm{nthSeries}\,q$ is a unit times $\prod_{a,b<q}\bigl(X - C([a]\,\mathrm{originParam}\,\chi_P \oplus [b]\,\mathrm{originParam}\,\chi_Q)\bigr)$, the combinations being formed in the maximal-ideal-adic sense.
--
--   This is the bridge from a Drinfeld $\Gamma(q)$-basis on the projective model, in the sense of an equality of divisors of $q$-torsion, to a Drinfeld basis of the formal group of $W$ over a complete local base with supersingular reduction, in the style of Katz–Mazur's theory of level structures. It is used in the construction of universal level structures over the completed local rings of the moduli problem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_IsDrinfeldBasis_exists_reducesToOrigin_isDrinfeldBasisAdic_of_toPowerSeries_eq_typeZero.lean

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

theorem WeierstrassCurve.DrinfeldGlobal.IsDrinfeldBasis.exists_reducesToOrigin_isDrinfeldBasisAdic_of_toPowerSeries_eq_typeZero
    {T : Type} [CommRing T] [IsLocalRing T] [IsNoetherianRing T] [IsAdicComplete (maximalIdeal T) T]
    (W : WeierstrassCurve T) [W.IsElliptic]

    (F : FormalGroup T) (hFW : F.toPowerSeries = W.formalGroupLawFixed)
    (G : RelativeGroupLaw T (projModelStrCR W))
    (hGpts : ∃ ev, IsPointsEval W G ev)
    (hGone : ∃ χ : OriginChartRing W →+* T,
      IsOriginChartSection (G.one (𝟙 _)) χ ∧ χ (xOverY W) = 0 ∧ χ (zOverY W) = 0)
    (q : ℕ) [Fact q.Prime]

    (hss : (W.map (residue T)).formalGroup.IsDrinfeldBasisAdic ⊥ q 0 0)
    (P Q : Section W) (hPQ : IsDrinfeldBasis G q P Q) :
    ∃ (χP χQ : OriginChartRing W →+* T),
      ReducesToOrigin P χP (maximalIdeal T) ∧ ReducesToOrigin Q χQ (maximalIdeal T) ∧
      F.IsDrinfeldBasisAdic (maximalIdeal T) q (originParam χP) (originParam χQ) := by sorry
