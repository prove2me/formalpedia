-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_variableChange_curve_eq_level_fst_eq_of_moduliPoint_mk_eq_of_raw_rigidDataH1Pow
-- name    : WeierstrassCurve.DrinfeldGlobal.exists_variableChange_curve_eq_level_fst_eq_of_moduliPoint_mk_eq_of_raw_rigidDataH1Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/0a7effaa-f544-5d29-8fd4-6cb94733d6f5
-- title:
--   Equal Γ₀(M')-moduli points give a common change of variables
-- statement:
--   Fix a commutative ring $A$, naturals $\ell_g$, $M'$, $q$ with $M'$ nonzero, and three transport hypotheses, each quantified over all $A$-algebras $T$: $h_\ell$ says that if a level datum $D=(x_P,y_P,x_Q,y_Q)$ over $T$ is a $\Gamma_1(\ell_g)$-point of $W$ (that is, $(x_P,y_P)$ satisfies the affine equation of $W$, the division polynomial $W.\mathrm{pre}\Psi\,\ell_g$ vanishes at $x_P$, and $x_Q=x_P$, $y_Q=y_P$) then its translate `D.variableChange C` is a $\Gamma_1(\ell_g)$-point of $C\bullet W$; $h_M$ says that the predicate `IsGamma0PowAt` at $(p,k)$ is carried by `kernelVariableChangeDeg C (gamma0PowDeg p k)`; and $h_L$ says that divisors of `inLineMulPoly W ℓg n x` are carried, after `kernelVariableChangeDeg C d`, to divisors of `inLineMulPoly (C • W) ℓg n (((C.u⁻¹)^2)(x - C.r))`. Fix further relative group laws $\mathcal G$ on projective Weierstrass models over $A$-algebras and a level transport $\mathcal T$ for $\mathcal G$ at $q$, and an algebraically closed $A$-field $\kappa$ with decidable equality in which $M'\ne 0$. Let $x,x'$ be raw points of the rigid datum `rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯` over $\kappa$, each consisting of a Weierstrass curve with unit discriminant together with a level object satisfying the levelness condition, and let $g$, $g'$ be affine points of $x.\mathrm{curve}$, $x'.\mathrm{curve}$. Assume of $g$ (and likewise of $g'$) that $g$ has additive order $M'$ and that for every prime factor $p$ of $M'$, every $n$ and every nonsingular affine point $(x_1,y_1)$ with $n\cdot g=(x_1,y_1)$ of order $p^{v_p(M')}$, the polynomial $x.\mathrm{level}.1\,p$ vanishes at $x_1$. Assume finally that the two pairs (curve with its ellipticity, together with the order-$M'$ point) define the same class in the quotient $\mathrm{ModuliPoint}\,M'\,\kappa$ of $\Gamma_0(M')$-pairs by the step relation. Then there is a change of variables $C_0$ over $\kappa$ such that acting by $C_0$ on $x$ within the rigid datum yields a point whose curve equals $x'.\mathrm{curve}$ and whose first level component equals $x'.\mathrm{level}.1$.
--
--   This is a rigidity statement in the style of Katz–Mazur: the $\Gamma_0(M')$-moduli class of an elliptic curve with a cyclic point of order $M'$ determines the curve together with the family of kernel polynomials indexed by the prime factors of $M'$, up to a single change of variables. Nothing is asserted about the $\Gamma_1(\ell_g)$-part or the Drinfeld level part of the level object; those are matched separately. It feeds the comparison of full-level and diamond-operator data for the datum `rigidDataH1Pow`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_exists_variableChange_curve_eq_level_fst_eq_of_moduliPoint_mk_eq_of_raw_rigidDataH1Pow.lean

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

set_option autoImplicit false

open ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel
open scoped Classical

theorem WeierstrassCurve.DrinfeldGlobal.exists_variableChange_curve_eq_level_fst_eq_of_moduliPoint_mk_eq_of_raw_rigidDataH1Pow
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
    (g : (x.curve).toAffine.Point) (g' : (x'.curve).toAffine.Point)
    (hg : (addOrderOf g = M' ∧
        ∀ (p : ↥M'.primeFactors) (n : ℕ) (x₁ y₁ : κ) (h₁ : (x.curve).toAffine.Nonsingular x₁ y₁),
          n • g = WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ → addOrderOf (n • g) = (p : ℕ) ^ M'.factorization (p : ℕ) →
          (x.level.1 p).IsRoot x₁))
    (hg' : (addOrderOf g' = M' ∧
        ∀ (p : ↥M'.primeFactors) (n : ℕ) (x₁ y₁ : κ) (h₁ : (x'.curve).toAffine.Nonsingular x₁ y₁),
          n • g' = WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ → addOrderOf (n • g') = (p : ℕ) ^ M'.factorization (p : ℕ) →
          (x'.level.1 p).IsRoot x₁))
    (heq : (Quot.mk _ (⟨x.curve, ⟨x.isUnit_Δ⟩, g, hg.1⟩ : ModularCurve.Gamma0Pair M' κ) : ModularCurve.ModuliPoint M' κ) =
      Quot.mk _ (⟨x'.curve, ⟨x'.isUnit_Δ⟩, g', hg'.1⟩ : ModularCurve.Gamma0Pair M' κ)) :
    ∃ C₀ : WeierstrassCurve.VariableChange κ,
      ((WeierstrassCurve.DrinfeldGlobal.rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).act C₀ x).curve = x'.curve ∧ ((WeierstrassCurve.DrinfeldGlobal.rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).act C₀ x).level.1 = x'.level.1 := by sorry
