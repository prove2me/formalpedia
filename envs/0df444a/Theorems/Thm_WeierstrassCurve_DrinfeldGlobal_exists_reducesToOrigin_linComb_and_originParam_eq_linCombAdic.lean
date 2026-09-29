-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_reducesToOrigin_linComb_and_originParam_eq_linCombAdic
-- name    : WeierstrassCurve.DrinfeldGlobal.exists_reducesToOrigin_linComb_and_originParam_eq_linCombAdic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/f5185a00-37ce-58a6-9495-f27b08889fae
-- title:
--   Origin parameter of [a]P+[b]Q is a formal linear combination
-- statement:
--   Let $T$ be a commutative Noetherian local ring that is complete with respect to its maximal ideal, let $W$ be a Weierstrass curve over $T$ that is elliptic, and let $F$ be a formal group over $T$ whose underlying two-variable power series is $W$'s fixed formal group law `W.formalGroupLawFixed`. Let $G$ be a relative group law on the structure morphism $\mathrm{Proj}$ of the graded projective model of $W$ over $\operatorname{Spec} T$, i.e. a fibrewise functorial multiplication, unit and inversion on $T$-scheme points satisfying the group axioms and compatible with base change, and assume: (i) there is an identification `ev` of the points of this model over any field $F'$ over $T$ with the affine points of $W$ base-changed to $F'$ which is additive for `G.mul` and equivariant for Galois twists; (ii) there is a ring homomorphism from the origin chart ring `OriginChartRing W` (degree-zero homogeneous localisation of the model away from the middle coordinate) to $T$ which is an origin-chart section of `G.one (𝟙 _)` and kills both `xOverY W` and `zOverY W`. Let $P,Q$ be sections of the model over the identity of the base, and let $\chi_P,\chi_Q$ be ring homomorphisms from the origin chart ring to $T$ with `ReducesToOrigin` for the maximal ideal: each is an origin-chart section of the corresponding section, and both its origin parameter $-\chi(\mathtt{xOverY}\,W)$ and $\mathtt{originW}\,\chi$ lie in the maximal ideal. Then for all $a,b\in\mathbb{N}$ there is a ring homomorphism $\chi$ from the origin chart ring to $T$ which reduces to the origin in this sense for the section $G.\mathrm{mul}\,(G.\mathrm{nsmul}\,a\,P)\,(G.\mathrm{nsmul}\,b\,Q)$, and whose origin parameter equals $F.\mathrm{eval}(F.\mathrm{evalNSMul}\,a\,(\mathrm{originParam}\,\chi_P),\,F.\mathrm{evalNSMul}\,b\,(\mathrm{originParam}\,\chi_Q))$, the evaluation being taken with respect to the adic topology of the maximal ideal.
--
--   This is the statement that, on a complete local base, the origin parameter is a homomorphism from integral linear combinations of sections reducing to the origin to the corresponding formal-group combinations, as in the classical comparison of the group law on an elliptic curve with its formal group. It is used in the construction of formal Drinfeld bases from global Drinfeld bases with supersingular reduction, and in the computation of the action of level automorphisms on origin parameters.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_exists_reducesToOrigin_linComb_and_originParam_eq_linCombAdic.lean

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

theorem WeierstrassCurve.DrinfeldGlobal.exists_reducesToOrigin_linComb_and_originParam_eq_linCombAdic
    {T : Type} [CommRing T] [IsLocalRing T] [IsNoetherianRing T] [IsAdicComplete (maximalIdeal T) T]
    (W : WeierstrassCurve T) [W.IsElliptic]
    (F : FormalGroup T) (hFW : F.toPowerSeries = W.formalGroupLawFixed)
    (G : RelativeGroupLaw T (projModelStrCR W))
    (hGpts : ∃ ev, IsPointsEval W G ev)
    (hGone : ∃ χ : OriginChartRing W →+* T,
      IsOriginChartSection (G.one (𝟙 _)) χ ∧ χ (xOverY W) = 0 ∧ χ (zOverY W) = 0)
    (P Q : Section W) (χP χQ : OriginChartRing W →+* T)
    (hP : ReducesToOrigin P χP (maximalIdeal T)) (hQ : ReducesToOrigin Q χQ (maximalIdeal T)) (a b : ℕ) :
    ∃ χ : OriginChartRing W →+* T, ReducesToOrigin (linComb G P Q a b) χ (maximalIdeal T) ∧
      originParam χ = F.linCombAdic (maximalIdeal T) (originParam χP) (originParam χQ) a b := by sorry
