-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_isUnit_inLineMulPoly_eq_C_mul_of_isSectionThrough_zsmulSection
-- name    : WeierstrassCurve.DrinfeldGlobal.exists_isUnit_inLineMulPoly_eq_C_mul_of_isSectionThrough_zsmulSection
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/453f863b-7a28-5635-b9a4-e3d47eed11c6
-- title:
--   Diamond invariance of the in-line product polynomial for sections
-- statement:
--   Let $A$ be a commutative ring and let $\mathcal{G}$ be a family assigning, to every commutative $A$-algebra $T$, every Weierstrass cubic $W$ in projective form over $T$ and every proof that $\Delta_W$ is a unit, a relative group law on the projective model of $W$ over $\operatorname{Spec} T$. Assume $\mathcal{G}$ is chord–tangent, i.e. for all such $T,W,\Delta_W$ the group law admits a points-evaluation datum `ev` witnessing `IsPointsEval`, and that its identity is the origin, i.e. for all such $T,W,\Delta_W$ there is a ring homomorphism from the origin chart ring of $W$ to $T$ which is an origin-chart section of $\mathcal{G}$'s unit section and kills both $x/y$ and $z/y$. Let $\ell$ be a prime with $\ell \neq 2$, let $T$ be a commutative $A$-algebra in which $\ell$ is invertible, and let $W$ be a Weierstrass cubic in projective form over $T$ with $\Delta_W$ a unit. Let $S$ be a section of the projective model over $\operatorname{Spec} T$, and let $x,y \in T$ be such that $S$ factors through the $z$-chart via a ring homomorphism sending $x/z \mapsto x$ and $y/z \mapsto y$; assume $(\,W.\mathrm{pre}\Psi_\ell)(x) = 0$. Let $a$ be an integer with $\ell \nmid a$, and let $x',y' \in T$ present, in the same way, the section $a \cdot S$ formed from $\mathcal{G}$ (the $k$-fold sum for $a = k \geq 0$, the inverse of the $(k+1)$-fold sum for $a = -(k+1)$). Then for every natural number $n$ there is a unit $u \in T$ with $$\prod_{b=1}^{(\ell-1)/2}\bigl(\Phi_n \cdot \Psi_b^2(x') - \Phi_b(x')\cdot \Psi_n^2\bigr) \;=\; u \cdot \prod_{b=1}^{(\ell-1)/2}\bigl(\Phi_n \cdot \Psi_b^2(x) - \Phi_b(x)\cdot \Psi_n^2\bigr)$$ as polynomials in $T[X]$, these products being [`ModularCurve.inLineMulPoly W ℓ n x'`](def/ModularCurve_WeierstrassH1Pow.html#L18) and [`ModularCurve.inLineMulPoly W ℓ n x`](def/ModularCurve_WeierstrassH1Pow.html#L18).
--
--   This is the section-theoretic form, valid over an arbitrary test algebra rather than a field, of the statement that the polynomial cutting out the multiples of an $\ell$-torsion point lying on a given line changes only by a unit when the point is replaced by $a$ times itself; it is the compatibility underlying the action of the diamond operators. It is used in the level-relabelling package, where $\Gamma_0$-relabelling must be shown to preserve the link between the $\Gamma_0$-tuple and the $\Gamma_1(\ell)$-point of the rigid moduli problem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_exists_isUnit_inLineMulPoly_eq_C_mul_of_isSectionThrough_zsmulSection.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_ModularCurve_LevelRelabelling
import Definitions.Def_ModularCurve_WeierstrassH1Pow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry ModularCurve WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal

theorem WeierstrassCurve.DrinfeldGlobal.exists_isUnit_inLineMulPoly_eq_C_mul_of_isSectionThrough_zsmulSection
    {A : Type} [CommRing A] (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2)
    (T : Type) [CommRing T] [Algebra A T] (hℓT : IsUnit ((ℓ : ℕ) : T))
    (W : WeierstrassCurve.Projective T) (hΔ : IsUnit W.Δ)
    (S : Section W) (x y : T) (hS : IsSectionThrough S x y) (hx : (W.preΨ ℓ).eval x = 0)
    (a : ℤ) (ha : ¬ ((ℓ : ℤ) ∣ a))
    (x' y' : T) (hS' : IsSectionThrough (ModularCurve.LevelRelabelling.zsmulSection (𝒢 T W hΔ) a S) x' y')
    (n : ℕ) :
    ∃ u : T, IsUnit u ∧ ModularCurve.inLineMulPoly W ℓ n x' = Polynomial.C u * ModularCurve.inLineMulPoly W ℓ n x := by sorry
