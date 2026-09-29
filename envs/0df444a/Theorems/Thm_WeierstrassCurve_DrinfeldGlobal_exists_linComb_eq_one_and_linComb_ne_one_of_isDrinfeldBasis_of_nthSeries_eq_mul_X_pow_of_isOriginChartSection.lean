-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_linComb_eq_one_and_linComb_ne_one_of_isDrinfeldBasis_of_nthSeries_eq_mul_X_pow_of_isOriginChartSection
-- name    : WeierstrassCurve.DrinfeldGlobal.exists_linComb_eq_one_and_linComb_ne_one_of_isDrinfeldBasis_of_nthSeries_eq_mul_X_pow_of_isOriginChartSection
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/40c4227a-cd9b-593e-846d-38374388d29e
-- title:
--   Existence of a unimodular pair with one relation for a Drinfeld basis
-- statement:
--   Let $q$ be a prime, $k$ a field of characteristic $q$, and $W$ an elliptic Weierstrass curve over $k$; let $G$ be a relative group law on the structure morphism $\mathrm{projModelStrCR}\,W$ of the projective model of $W$ over $\operatorname{Spec} k$, i.e. a functorial group structure on the sets of scheme morphisms over $\operatorname{Spec} k$, together with naturality of multiplication under base change. Assume: (i) there is a points-evaluation witness $ev$ for $G$, namely a family of bijections, for each field $F$ that is a $k$-algebra, between $F$-points of the projective model over $\operatorname{Spec} F$ and the affine Mordell–Weil group $(W_F)(F)$, carrying $G$-multiplication to addition and compatible with the Galois twist; (ii) the unit section $G.\mathrm{one}(\mathbf 1)$ is an origin chart section, i.e. it factors as $\operatorname{Spec}$ of a ring homomorphism $\chi$ from the chart ring $\mathrm{Away}$ at the coordinate $Y$ followed by the chart inclusion, for some $\chi$ killing both $X/Y$ and $Z/Y$; (iii) $F$ is a formal group over $k$ whose bivariate power series is $W.\mathrm{formalGroupLawFixed}$, and its $q$-th iterated series $F.\mathrm{nthSeries}\,q$ (defined by $0$ at $0$ and $s_{n+1} = F(s_n, X)$) equals a unit times $X^q$; (iv) $P,Q$ are sections of the projective model over $\operatorname{Spec} k$ forming a Drinfeld basis of level $q$ for $G$, meaning that the ideal sheaf data $\mathrm{basisDivisor}\,G\,q\,P\,Q$ coincides with the $q$-torsion ideal $\mathrm{torsionIdeal}\,G\,q$. Then there exist $a,b,c,d \in \mathbb{N}$ such that $ad-bc$ is a unit in $\mathbb{Z}/q$, while $[a]P + [b]Q$ equals the unit section and $[c]P + [d]Q$ does not, where $[a]P + [b]Q$ denotes $\mathrm{linComb}\,G\,P\,Q\,a\,b = G.\mathrm{mul}(G.\mathrm{nsmul}\,a\,P,\ G.\mathrm{nsmul}\,b\,Q)$.
--
--   This is the normal-position step for a Drinfeld basis of level $q$ on an ordinary elliptic curve in characteristic $q$: the relation lattice of $(P,Q)$ inside $(\mathbb{Z}/q)^2$ is a line, and the conclusion records a unimodular pair consisting of a vector in that line and a vector outside it. It is used in the construction of the level structures attached to the modular curves of level $\Gamma_0$-type, where such a pair produces the required isomorphism with an adjoined root of a power series.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_exists_linComb_eq_one_and_linComb_ne_one_of_isDrinfeldBasis_of_nthSeries_eq_mul_X_pow_of_isOriginChartSection.lean

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

open AlgebraicGeometry CategoryTheory WeierstrassProjModel IsLocalRing
open WeierstrassCurve.DrinfeldGlobal

attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.exists_linComb_eq_one_and_linComb_ne_one_of_isDrinfeldBasis_of_nthSeries_eq_mul_X_pow_of_isOriginChartSection
    {k : Type} [Field k] (q : ℕ) [Fact q.Prime] [CharP k q]
    (W : WeierstrassCurve k) [W.IsElliptic]
    (G : RelativeGroupLaw k (projModelStrCR W))
    (hG : ∃ ev, IsPointsEval W G ev)

    (hGO : ∃ χ : OriginChartRing W →+* k,
      IsOriginChartSection (G.one (𝟙 (base (T := k)))) χ ∧ χ (xOverY W) = 0 ∧ χ (zOverY W) = 0)

    (F : FormalGroup k) (hFW : F.toPowerSeries = W.formalGroupLawFixed)
    (hord : ∃ u : PowerSeries k, IsUnit u ∧ F.nthSeries q = u * PowerSeries.X ^ q)
    (P Q : Section W) (hPQ : IsDrinfeldBasis G q P Q) :
    ∃ a b c d : ℕ, IsUnit (((a * d : ℤ) - (b * c : ℤ) : ℤ) : ZMod q) ∧
      linComb G P Q a b = G.one (𝟙 (base (T := k))) ∧
      linComb G P Q c d ≠ G.one (𝟙 (base (T := k))) := by sorry
