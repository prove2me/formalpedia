-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_isDrinfeldBasis_iff_eval_originParam_eq_zero_and_exists_section_of_nthSeries_eq_X_mul_mul_of_forall_nthSeries_eq_mul_prod
-- name    : WeierstrassCurve.DrinfeldGlobal.isDrinfeldBasis_iff_eval_originParam_eq_zero_and_exists_section_of_nthSeries_eq_X_mul_mul_of_forall_nthSeries_eq_mul_prod
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/be3feec7-62fc-5fcd-85e5-9856fe8ba2d5
-- title:
--   Drinfeld bases and roots of the Igusa factor g
-- statement:
--   Let $T$ be a Noetherian local ring, complete with respect to its maximal ideal $\mathfrak m$, let $q$ be a prime with $q \in \mathfrak m$, and let $W$ be a Weierstrass curve over $T$ that is elliptic. Let $G$ be a relative group law on the structural morphism $\mathrm{Proj} \to \operatorname{Spec} T$ of the projective model of $W$, assumed to admit a points-evaluation family of bijections, for every field $F$ over $T$, between $F$-sections and the affine points of $W_F$ that is additive and Galois-equivariant, and assumed to have a unit section given by a ring homomorphism $\chi$ from the origin chart to $T$ killing both $x/y$ and $z/y$. Let $F$ be a formal group over $T$ whose bivariate series is the fixed Weierstrass formal group law of $W$, and write $[q]_F$ for its $q$-th iterate (defined by $[0]_F = 0$, $[n+1]_F = F([n]_F, X)$). Assume a factorisation $[q]_F = X \cdot g \cdot v$ with $g \in T[X]$ monic of degree $q-1$ whose coefficients in degrees $< q-1$ lie in $\mathfrak m$, and $v$ a unit power series. Let $Q$ be a $T$-section with $q \cdot Q$ equal to the unit section which, for no ring homomorphism $\chi$ from the origin chart to $T$, reduces to the origin modulo $\mathfrak m$ (that is, no $\chi$ both represents $Q$ in the origin chart and has $-\chi(x/y), -\chi(z/y) \in \mathfrak m$). Assume finally that for every $\pi \in \mathfrak m$ with $g(\pi) = 0$ there is a unit $u$ in $T[[X]]$ with $[q]_F = u \prod_{a < q}\bigl(X - [a]_F(\pi)\bigr)$, the values $[a]_F(\pi)$ being formed by iterated evaluation of $F$ at $\pi$. Then: (i) for every section $P$ and every $\chi_P$ with $P$ represented by $\chi_P$ in the origin chart and $\pi_P := -\chi_P(x/y)$, $-\chi_P(z/y) \in \mathfrak m$, the pair $(P,Q)$ is a Drinfeld basis for $G$ and $q$ — equality of the divisor attached to the tuple built from $P, Q$ with the kernel ideal sheaf of multiplication by $q$ — if and only if $g(\pi_P) = 0$; and (ii) every $\pi \in T$ with $g(\pi) = 0$ arises as $\pi_P = -\chi_P(x/y)$ for some section $P$ represented by some $\chi_P$ with $-\chi_P(x/y), -\chi_P(z/y) \in \mathfrak m$.
--
--   This is the dictionary identifying the Drinfeld $\Gamma(q)$-partners of a $q$-torsion section not reducing to the origin with the roots of the Igusa factor $g$ of the $q$-division series of the formal group, together with the surjectivity of the origin-parameter map onto those roots. It is used in the construction of the moduli interpretation of level structures, where the roots of $g$ are produced over an explicit algebra such as $T[X]/(g)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_isDrinfeldBasis_iff_eval_originParam_eq_zero_and_exists_section_of_nthSeries_eq_X_mul_mul_of_forall_nthSeries_eq_mul_prod.lean

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

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal IsLocalRing Polynomial

attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.isDrinfeldBasis_iff_eval_originParam_eq_zero_and_exists_section_of_nthSeries_eq_X_mul_mul_of_forall_nthSeries_eq_mul_prod
    {T : Type} [CommRing T] [IsLocalRing T] [IsNoetherianRing T] [IsAdicComplete (maximalIdeal T) T]
    (q : ℕ) [Fact q.Prime] (hqT : (q : T) ∈ maximalIdeal T)
    (W : WeierstrassCurve T) [W.IsElliptic]
    (G : RelativeGroupLaw T (projModelStrCR W))
    (hG : ∃ ev, IsPointsEval W G ev)
    (hGO : ∃ χ : OriginChartRing W →+* T,
      IsOriginChartSection (G.one (𝟙 _)) χ ∧ χ (xOverY W) = 0 ∧ χ (zOverY W) = 0)
    (F : FormalGroup T) (hFW : F.toPowerSeries = W.formalGroupLawFixed)

    (g : T[X]) (hgm : g.Monic) (hgdeg : g.natDegree = q - 1) (hgcoeff : ∀ i < q - 1, g.coeff i ∈ maximalIdeal T)
    (v : PowerSeries T) (hv : IsUnit v)
    (hfacq : F.nthSeries q = PowerSeries.X * (↑g : PowerSeries T) * v)

    (Q : Section W) (hQq : G.nsmul (𝟙 (base (T := T))) q Q = G.one (𝟙 (base (T := T))))
    (hQ : ∀ χ : OriginChartRing W →+* T, ¬ ReducesToOrigin Q χ (maximalIdeal T))

    (hfull : ∀ π : T, π ∈ maximalIdeal T → g.eval π = 0 →
      ∃ u : PowerSeries T, IsUnit u ∧
        F.nthSeries q = u * ∏ a ∈ Finset.range q,
          (PowerSeries.X - PowerSeries.C (letI : WithIdeal T := ⟨maximalIdeal T⟩; F.evalNSMul a π))) :
    (∀ (P : Section W) (χP : OriginChartRing W →+* T), ReducesToOrigin P χP (maximalIdeal T) →
        (IsDrinfeldBasis G q P Q ↔ g.eval (originParam χP) = 0)) ∧
    (∀ π : T, g.eval π = 0 →
        ∃ (P : Section W) (χP : OriginChartRing W →+* T), ReducesToOrigin P χP (maximalIdeal T) ∧ originParam χP = π) := by sorry
