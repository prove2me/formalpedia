-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_moduleFinite_represents_isLevel
-- name    : WeierstrassCurve.DrinfeldGlobal.exists_moduleFinite_represents_isLevel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/bdc65fe1-f88a-555b-b37c-632b7754a8a8
-- title:
--   Finite representability of the raw Drinfeld Γ(q)-pair functor
-- statement:
--   Fix a commutative ring $A$ (in universe $u$) and a prime $q$, together with: a family $\mathcal G$ of group laws assigning to every $A$-algebra $T$, every projective Weierstrass curve $W/T$ and every proof that $\Delta_W$ is a unit a relative group law on the projective model of $W$; the hypothesis `GroupLaws.IsChordTangent` that each such group law admits an evaluation equivalence $\mathrm{ev}$ with `IsPointsEval`; the hypothesis `GroupLaws.IsOriginIdentity` that for each such datum there is a ring homomorphism from the origin chart ring to $T$ cutting out the unit section and annihilating $x/y$ and $z/y$; a level transport datum $\mathcal T$ (functorial transport of raw Drinfeld pairs along $A$-algebra maps and variable changes, preserving the level condition) satisfying `LevelTransport.IsSectionTransport`, i.e. its action on curves is the expected one and its sections pull back correctly along `Proj.map` of the graded comparison homomorphisms; and the two existence hypotheses `hVC`, `hCO` providing, for every variable change and every coefficient ring map, a graded homomorphism of projective-model gradings satisfying the irrelevant-ideal inequality and realising the standard formulas $X_0\mapsto u^2X_0+rX_2$, $X_1\mapsto u^3X_1+u^2sX_0+tX_2$, $X_2\mapsto X_2$ (respectively acting as $f$ on constants and fixing the $X_i$). Let $B$ be an $A$-algebra and $W$ a Weierstrass curve over $B$ with $\Delta_W$ a unit. Then there exists a commutative ring $C$ that is an $A$-algebra and a $B$-algebra, with the two structures compatible and with $C$ finite as a $B$-module, and a raw Drinfeld pair $x_u$ over $C$ (a projective Weierstrass curve with two sections) whose curve is $W\otimes_BC$ and whose two sections form a Drinfeld basis of level $q$ for the group law $\mathcal G$, such that for every $A$-algebra $T$, every $A$-algebra map $\varphi:B\to T$ and every raw Drinfeld pair $x$ over $T$: $x$ is a level-$q$ Drinfeld structure on $W\otimes_\varphi T$ if and only if there is a unique $A$-algebra map $\psi:C\to T$ with $\psi\circ(\text{structure map }B\to C)=\varphi$ and $\mathcal T.\mathrm{map}\,\psi\,x_u=x$.
--
--   This is the representability statement for Drinfeld $\Gamma(q)$-level structures on a fixed elliptic Weierstrass curve over a base, in the form of a universal finite algebra over the Weierstrass base (Katz–Mazur). It is used in the construction of the rigid data for the full-level moduli problems, being cited by the $\Gamma_0$- and $\Gamma_1$-power representability results for raw rigid data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_exists_moduleFinite_represents_isLevel.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal

attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.exists_moduleFinite_represents_isLevel
    {A : Type u} [CommRing A] (q : ℕ) [Fact q.Prime]
    (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (𝒯 : LevelTransport A 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)
    (hVC : ∀ (T : Type u) [CommRing T] (W : WeierstrassCurve.Projective T) (C : WeierstrassCurve.VariableChange T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (C • W))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ), IsVariableChangeHom W C φ)
    (hCO : ∀ (T T' : Type u) [CommRing T] [CommRing T'] (W : WeierstrassCurve.Projective T) (f : T →+* T'),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ), IsCoefficientHom W f φ)
    (B : Type u) [CommRing B] [Algebra A B] (W : WeierstrassCurve B) (hΔ : IsUnit W.Δ) :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra A C) (_ : Algebra B C) (_ : IsScalarTower A B C)
      (_ : Module.Finite B C) (xᵤ : RawDrinfeldPair C)
      (_ : RawDrinfeldPair.IsLevel 𝒢 q (W.map (algebraMap B C)) xᵤ),
      ∀ (T : Type u) [CommRing T] [Algebra A T] (φ : B →ₐ[A] T) (x : RawDrinfeldPair T),
        RawDrinfeldPair.IsLevel 𝒢 q (W.map φ.toRingHom) x ↔
          ∃! ψ : C →ₐ[A] T, ψ.toRingHom.comp (algebraMap B C) = φ.toRingHom ∧ 𝒯.map ψ xᵤ = x := by sorry
