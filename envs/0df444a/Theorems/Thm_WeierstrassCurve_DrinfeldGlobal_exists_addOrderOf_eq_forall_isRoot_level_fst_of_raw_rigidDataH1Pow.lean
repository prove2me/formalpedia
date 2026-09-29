-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_addOrderOf_eq_forall_isRoot_level_fst_of_raw_rigidDataH1Pow
-- name    : WeierstrassCurve.DrinfeldGlobal.exists_addOrderOf_eq_forall_isRoot_level_fst_of_raw_rigidDataH1Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/a581cc63-e098-5711-a7dc-d6ad93aa0256
-- title:
--   Cyclic generator of order M' cut by the Γ₀(M')-tuple
-- statement:
--   Let $A$ be a commutative ring and $\ell g, M', q$ natural numbers with $M'$ nonzero. Assume three transport hypotheses, each quantified over all commutative $A$-algebras $T$ and all Weierstrass variable changes $C$ over $T$: that the $\Gamma_1$-point condition [`ModularCurve.IsGamma1Point`](def/ModularCurve_WeierstrassGamma1Pow.html#L10) for level $\ell g$ ($(x_P,y_P)$ satisfying the affine equation, $(W.\mathrm{pre}\Psi\,\ell g)(x_P)=0$, $x_Q=x_P$, $y_Q=y_P$) is preserved by $C$ acting on curve and `LevelPData`; that [`ModularCurve.IsGamma0PowAt W p k h`](def/ModularCurve_WeierstrassGamma0Pow.html#L55) (an `IsTwoKernel` condition when $p^k=2$, an `IsCyclicGenKernel` condition otherwise) is preserved when $h$ is replaced by [`ModularCurve.kernelVariableChangeDeg C (gamma0PowDeg p k) h`](def/ModularCurve_WeierstrassLevelComponents.html#L104); and that divisibility of [`ModularCurve.inLineMulPoly W ℓg n x`](def/ModularCurve_WeierstrassH1Pow.html#L18) by $h$ is carried, under the same substitution, to divisibility of the corresponding polynomial for $C \bullet W$ at $((C.u^{-1})^2(x-C.r))$. Let further $\mathcal G$ be a system of relative group laws over $A$, $\mathcal T$ a level transport of level $q$, and $\kappa$ an algebraically closed field that is an $A$-algebra in which $M'$ is invertible, i.e. $M' \ne 0$ in $\kappa$. Let $x$ be a raw datum over $\kappa$ for `rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯`: a Weierstrass curve $x.\mathrm{curve}$ over $\kappa$ with unit discriminant, together with a level structure consisting of a family of polynomials $h_p$ indexed by the prime factors $p$ of $M'$ with `IsGamma0PowAt` at $(p, v_p(M'))$, a `LevelPData` which is a $\Gamma_1$-point of level $\ell g$, and a Drinfeld level-$q$ datum, subject to the link condition [`ModularCurve.IsGamma1Link`](def/ModularCurve_WeierstrassH1Pow.html#L26). Then there is a point $g$ of the affine group $x.\mathrm{curve}.\mathrm{toAffine}.\mathrm{Point}$ whose additive order is exactly $M'$ and which has the property that for every prime factor $p$ of $M'$, every $n$, and every affine point $(x_1,y_1)$ nonsingular on the curve with $n \cdot g = (x_1,y_1)$ and $\mathrm{ord}(n\cdot g) = p^{v_p(M')}$, the value $x_1$ is a root of the $p$-th component $h_p = x.\mathrm{level}.1\,p$.
--
--   This is the step which converts the $\Gamma_0(M')$-component of an $H_1$-rigid point (level $\Gamma_0(M') \cap \Gamma_1(\ell g)$ together with Drinfeld level $q$) into an honest cyclic subgroup of order $M'$ over an algebraically closed field: the kernel polynomials $h_p$ are realised as the $x$-coordinates of the multiples of a single generator $g$. It is used in the analysis of the diamond operators and of the reductions of such points, where the generator and its prime-power multiples must be compared across variable changes and specialisations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_exists_addOrderOf_eq_forall_isRoot_level_fst_of_raw_rigidDataH1Pow.lean

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

theorem WeierstrassCurve.DrinfeldGlobal.exists_addOrderOf_eq_forall_isRoot_level_fst_of_raw_rigidDataH1Pow
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
    (x : (WeierstrassCurve.DrinfeldGlobal.rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).Raw κ) :
    ∃ g : (x.curve).toAffine.Point, (addOrderOf g = M' ∧
        ∀ (p : ↥M'.primeFactors) (n : ℕ) (x₁ y₁ : κ) (h₁ : (x.curve).toAffine.Nonsingular x₁ y₁),
          n • g = WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ → addOrderOf (n • g) = (p : ℕ) ^ M'.factorization (p : ℕ) →
          (x.level.1 p).IsRoot x₁) := by sorry
