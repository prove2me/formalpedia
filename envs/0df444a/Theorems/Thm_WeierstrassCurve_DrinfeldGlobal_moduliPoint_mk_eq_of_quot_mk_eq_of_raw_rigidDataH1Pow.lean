-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_moduliPoint_mk_eq_of_quot_mk_eq_of_raw_rigidDataH1Pow
-- name    : WeierstrassCurve.DrinfeldGlobal.moduliPoint_mk_eq_of_quot_mk_eq_of_raw_rigidDataH1Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/cdfe3245-157b-5ca7-a31e-74779647d98b
-- title:
--   Equal raw H₁-classes with cut-out generators give equal moduli points
-- statement:
--   Fix a commutative ring $A$ and natural numbers $\ell_g, M', q$ with $M' \neq 0$. Three transport hypotheses are assumed, for every $A$-algebra $T$, Weierstrass curve $W$ over $T$ and variable change $C$: (hℓ) if a level-$P$ datum $D = (x_P,y_P,x_Q,y_Q)$ satisfies `IsGamma1Point` for $W$ and $\ell_g$ — that is, $(x_P,y_P)$ lies on the affine equation of $W$, $(W.\mathrm{pre}\Psi\,\ell_g)(x_P)=0$, $x_Q=x_P$ and $y_Q=y_P$ — then $D$ transported by $C$ satisfies it for $C \bullet W$; (hM) `IsGamma0PowAt` at $(p,k)$ (the two-kernel condition when $p^k=2$, else the cyclic-generator-kernel condition) is preserved on replacing $h$ by `kernelVariableChangeDeg` $C$ (`gamma0PowDeg` $p\,k$) $h$; (hL) divisibility $h \mid$ `inLineMulPoly` $W\,\ell_g\,n\,x$ transports to the $C$-twisted polynomial and the point $u^{-2}(x-r)$. Given group laws $\mathcal{G}$ on projective Weierstrass models over $A$-algebras with unit discriminant and a level transport $\mathcal{T}$ of raw Drinfeld pairs at $q$, let $\kappa$ be an algebraically closed $A$-algebra field with $M' \neq 0$ in $\kappa$, and let $x,x'$ be raw data over $\kappa$ for the rigid datum `rigidDataH1Pow` — each a Weierstrass curve with unit discriminant together with a level object satisfying the level condition — having the same class in the quotient `Pt` $\kappa$. Let $g$ on $x$'s curve and $g'$ on $x'$'s curve be affine points of additive order exactly $M'$ such that, for each prime factor $p$ of $M'$, every multiple $n \bullet g$ (resp. $n \bullet g'$) which is an affine point $(x_1,y_1)$ of order $p^{v_p(M')}$ has $x_1$ a root of the $p$-th polynomial of the $\Gamma_0$-power component of the level object of $x$ (resp. $x'$). Then the pairs $(x.\mathrm{curve}, g)$ and $(x'.\mathrm{curve}, g')$, viewed as `Gamma0Pair` $M'$ $\kappa$ via the ellipticity coming from unit discriminant and the order conditions, have the same class in `ModuliPoint` $M'$ $\kappa$, i.e. they agree up to a variable change together with multiplication of the generator by an integer coprime to $M'$.
--
--   This is the passage from the moduli interpretation of the $H_1$-type level datum (a $\Gamma_0(M')$-power component, a $\Gamma_1(\ell_g)$ component and a Drinfeld level component) to the coarse $\Gamma_0(M')$-moduli set: raw data with the same class and generators cut out by the $\Gamma_0$-power polynomials give the same moduli point. It is used in the study of the diamond/level automorphisms and of the $j$-invariant maps attached to `rigidDataH1Pow`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_moduliPoint_mk_eq_of_quot_mk_eq_of_raw_rigidDataH1Pow.lean

import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_ModularCurve_WeierstrassGamma1Pow
import Definitions.Def_ModularCurve_WeierstrassH1Pow
import Definitions.Def_ModularCurve_KatzLevelP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.DrinfeldGlobal.moduliPoint_mk_eq_of_quot_mk_eq_of_raw_rigidDataH1Pow
    (A : Type) [CommRing A] (ℓg M' q : ℕ) [NeZero M']
    (hℓ : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsGamma1Point W ℓg D →
        ModularCurve.IsGamma1Point (C • W) ℓg (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (hL : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (d n : ℕ) (h : Polynomial T) (x : T), h ∣ ModularCurve.inLineMulPoly W ℓg n x →
        ModularCurve.kernelVariableChangeDeg C d h ∣
          ModularCurve.inLineMulPoly (C • W) ℓg n (((C.u⁻¹ : Tˣ) : T) ^ 2 * (x - C.r)))
    (𝒢 : GroupLaws A) (𝒯 : LevelTransport A 𝒢 q)
    (κ : Type) [Field κ] [IsAlgClosed κ] [DecidableEq κ] [Algebra A κ] (hM'κ : ((M' : ℕ) : κ) ≠ 0)
    (x x' : (WeierstrassCurve.DrinfeldGlobal.rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).Raw κ)
    (hxx' : (Quot.mk _ x : (WeierstrassCurve.DrinfeldGlobal.rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).Pt κ) = Quot.mk _ x')
    (g : (x.curve).toAffine.Point) (g' : (x'.curve).toAffine.Point)
    (hg : (addOrderOf g = M' ∧
        ∀ (p : ↥M'.primeFactors) (n : ℕ) (x₁ y₁ : κ) (h₁ : (x.curve).toAffine.Nonsingular x₁ y₁),
          n • g = WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ → addOrderOf (n • g) = (p : ℕ) ^ M'.factorization (p : ℕ) →
          (x.level.1 p).IsRoot x₁))
    (hg' : (addOrderOf g' = M' ∧
        ∀ (p : ↥M'.primeFactors) (n : ℕ) (x₁ y₁ : κ) (h₁ : (x'.curve).toAffine.Nonsingular x₁ y₁),
          n • g' = WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ → addOrderOf (n • g') = (p : ℕ) ^ M'.factorization (p : ℕ) →
          (x'.level.1 p).IsRoot x₁)) :
    (Quot.mk _ (⟨x.curve, ⟨x.isUnit_Δ⟩, g, hg.1⟩ : ModularCurve.Gamma0Pair M' κ) : ModularCurve.ModuliPoint M' κ) =
      Quot.mk _ (⟨x'.curve, ⟨x'.isUnit_Δ⟩, g', hg'.1⟩ : ModularCurve.Gamma0Pair M' κ) := by sorry
