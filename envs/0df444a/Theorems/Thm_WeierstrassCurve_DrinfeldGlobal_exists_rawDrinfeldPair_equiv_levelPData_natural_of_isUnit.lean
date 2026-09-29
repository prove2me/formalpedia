-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_rawDrinfeldPair_equiv_levelPData_natural_of_isUnit
-- name    : WeierstrassCurve.DrinfeldGlobal.exists_rawDrinfeldPair_equiv_levelPData_natural_of_isUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/91074390-7c92-50f5-9e6e-3450d515b268
-- title:
--   Drinfeld Γ(q)-pairs versus Katz level-q data, naturally
-- statement:
--   Fix a prime $q \neq 2$ and a commutative ring $A_0$. Let $\mathcal{G}$ be a family of group laws assigning to every $A_0$-algebra $T$, every projective Weierstrass curve $W$ over $T$ and every witness that $\Delta_W$ is a unit a relative group law on the projective model of $W$; assume $\mathcal{G}$ is chord-tangent (each such group law admits a points-evaluation `ev` in the sense of `IsPointsEval`) and origin-identity (its unit section is cut out by a ring homomorphism from the origin chart killing $x/y$ and $z/y$). Let $\mathcal{T}$ be a level transport for $(\mathcal{G}, q)$, i.e. functorial base-change and variable-change operations on raw Drinfeld pairs (a curve together with two sections of its projective model over the base) preserving the predicate `RawDrinfeldPair.IsLevel`, and assume $\mathcal{T}$ is a section transport: the transported pairs carry the expected curve and their sections pull back to the original ones along the induced maps of Proj. The assertion is the existence of a family $\kappa$ which, for each $A_0$-algebra $T$ and Weierstrass curve $E$ over $T$ with $\Delta_E$ and $q$ units in $T$, is a bijection between the raw Drinfeld pairs $x$ with $x.\mathrm{curve} = E$ whose two sections form a Drinfeld basis of level $q$ for $\mathcal{G}$, and the quadruples $D = (x_P, y_P, x_Q, y_Q)$ in $T$ such that $(x_P,y_P)$ and $(x_Q,y_Q)$ satisfy the affine Weierstrass equation of $E$, the polynomial $\tilde\Psi_q$ of $E$ vanishes at $x_P$ and at $x_Q$, and both $\prod_{a=1}^{(q-1)/2}\bigl(x_Q\,\Psi_a^2(x_P) - \Phi_a(x_P)\bigr)$ and the same expression with $x_P$, $x_Q$ interchanged are units; together with naturality: for $A_0$-algebras $T, T'$, an $A_0$-algebra map $f : T \to T'$, a curve $E$ over $T$, unit witnesses for $\Delta_E$ and $q$ in $T$ and for $\Delta$ of the base-changed curve and $q$ in $T'$, and a level pair $x$ over $E$ whose transport $\mathcal{T}.\mathrm{map}\,f\,x$ is again of level $q$ over the base-changed curve, the quadruple attached by $\kappa$ to the transported pair is the coefficientwise image under $f$ of the quadruple attached to $x$.
--
--   This is the comparison, at an invertible odd level $q$, between Drinfeld bases of level $q$ for a fixed family of group laws on projective Weierstrass models and Katz-style level-$q$ data recorded in affine division-polynomial coordinates, in the shape of Katz–Mazur 1.10.11–1.10.12; the independence of the two points is expressed by the invertibility of the products built from the division polynomials. It supplies the dictionary used when counting level structures over an algebraically closed field, when lifting level structures along surjections with nilpotent kernel, and in the computation over dual numbers of the full-level moduli problem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_exists_rawDrinfeldPair_equiv_levelPData_natural_of_isUnit.lean

import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_KatzLevelP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel IsLocalRing

attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.exists_rawDrinfeldPair_equiv_levelPData_natural_of_isUnit
    (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2) (A₀ : Type) [CommRing A₀]
    (𝒢 : GroupLaws A₀) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (𝒯 : LevelTransport A₀ 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport) :
    ∃ κ : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (E : WeierstrassCurve T),
        IsUnit E.Δ → IsUnit ((q : ℕ) : T) →
          {x : RawDrinfeldPair T // RawDrinfeldPair.IsLevel 𝒢 q E x} ≃
            {D : ModularCurve.LevelPData T // ModularCurve.IsLevelPStructure E q D},
      ∀ (T T' : Type) [CommRing T] [Algebra A₀ T] [CommRing T'] [Algebra A₀ T'] (f : T →ₐ[A₀] T')
        (E : WeierstrassCurve T) (hΔ : IsUnit E.Δ) (hq : IsUnit ((q : ℕ) : T))
        (hΔ' : IsUnit (E.map f.toRingHom).Δ) (hq' : IsUnit ((q : ℕ) : T'))
        (x : RawDrinfeldPair T) (hx : RawDrinfeldPair.IsLevel 𝒢 q E x)
        (hx' : RawDrinfeldPair.IsLevel 𝒢 q (E.map f.toRingHom) (𝒯.map f x)),
        ((κ T' (E.map f.toRingHom) hΔ' hq' ⟨𝒯.map f x, hx'⟩ : {D : ModularCurve.LevelPData T' //
            ModularCurve.IsLevelPStructure (E.map f.toRingHom) q D}) : ModularCurve.LevelPData T') =
          ((κ T E hΔ hq ⟨x, hx⟩ : {D : ModularCurve.LevelPData T // ModularCurve.IsLevelPStructure E q D}) :
            ModularCurve.LevelPData T).map f.toRingHom := by sorry
