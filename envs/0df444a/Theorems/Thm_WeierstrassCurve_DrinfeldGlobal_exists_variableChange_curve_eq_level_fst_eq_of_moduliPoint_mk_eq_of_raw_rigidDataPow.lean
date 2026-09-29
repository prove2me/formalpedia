-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_variableChange_curve_eq_level_fst_eq_of_moduliPoint_mk_eq_of_raw_rigidDataPow
-- name    : WeierstrassCurve.DrinfeldGlobal.exists_variableChange_curve_eq_level_fst_eq_of_moduliPoint_mk_eq_of_raw_rigidDataPow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/589c7d0a-6817-50b6-b86a-70445ada85a2
-- title:
--   Aligning raw rigid data with equal Γ₀(M')-moduli class
-- statement:
--   Let $A$ be a commutative ring, let $\ell', M', q$ be natural numbers with $M' \neq 0$, and assume two variable-change compatibilities over $A$-algebras $T$: every level-$p$ datum $D$ that is a level-$\ell'$ structure for a Weierstrass curve $W$ (in the sense of [`ModularCurve.IsLevelPStructure`](def/ModularCurve_KatzLevelP.html#L104): the two points $P,Q$ satisfy the affine equation, their $x$-coordinates are roots of $W.\mathrm{pre\Psi}\,\ell'$, and the two independence elements are units) remains one for $C \bullet W$ after the coordinatewise transformation $D.\mathrm{variableChange}\,C$; and $\mathrm{IsGamma0PowAt}\,W\,p\,k\,h$ is preserved on passing to $C \bullet W$ and $\mathrm{kernelVariableChangeDeg}\,C\,(\mathrm{gamma0PowDeg}\,p\,k)\,h$. Let $\mathcal G$ be group laws on $A$ and $\mathcal T$ a level transport for $\mathcal G$ of level $q$, and write $R = \mathrm{rigidDataPow}\,A\,\ell'\,M'\,q\,h_\ell\,h_M\,\mathcal G\,\mathcal T$. Let $\kappa$ be an algebraically closed field which is an $A$-algebra and in which the image of $M'$ is nonzero. Let $x, x'$ be raw objects of $R$ over $\kappa$, each consisting of a Weierstrass curve with unit discriminant together with level data satisfying the level condition, and let $g$, $g'$ be affine points of $x.\mathrm{curve}$, $x'.\mathrm{curve}$. Assume of each of $g$, $g'$: its additive order is $M'$, and for every prime $p \mid M'$, every $n$, and every nonsingular affine point $(x_1,y_1)$ with $n \cdot g = (x_1,y_1)$ and $\mathrm{addOrderOf}(n\cdot g) = p^{v_p(M')}$, the element $x_1$ is a root of the $p$-th component of the first constituent $x.\mathrm{level}.1$ of the level data (resp. $x'.\mathrm{level}.1$). Assume finally that the $\Gamma_0(M')$-pairs $(x.\mathrm{curve}, g)$ and $(x'.\mathrm{curve}, g')$, each with its ellipticity witness and order condition, have the same class in $\mathrm{ModuliPoint}\,M'\,\kappa$, the quotient of $\Gamma_0(M')$-pairs by the relation that some variable change carries one curve to the other and the second generator is $k$ times the transported first generator for some $k$ coprime to $M'$. Then there exists a variable change $C_0$ over $\kappa$ such that $R.\mathrm{act}\,C_0\,x$ has curve equal to $x'.\mathrm{curve}$ and first level constituent equal to $x'.\mathrm{level}.1$.
--
--   This is the rigidity step turning an equality of $\Gamma_0(M')$-moduli classes into an actual alignment of the underlying rigidified data by a single Weierstrass variable change, at the level of the curve and of the $\Gamma_0(M')$-kernel polynomials; the remaining constituents of the level data are not addressed. It is used in the full-level analysis of points of the Drinfeld-style moduli problem attached to $\mathrm{rigidDataPow}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_exists_variableChange_curve_eq_level_fst_eq_of_moduliPoint_mk_eq_of_raw_rigidDataPow.lean

import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_ModularCurve_KatzLevelP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel
open scoped Classical

theorem WeierstrassCurve.DrinfeldGlobal.exists_variableChange_curve_eq_level_fst_eq_of_moduliPoint_mk_eq_of_raw_rigidDataPow
    (A : Type) [CommRing A] (ℓ' M' q : ℕ) [NeZero M']
    (hℓ : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ' D →
        ModularCurve.IsLevelPStructure (C • W) ℓ' (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (𝒢 : GroupLaws A) (𝒯 : LevelTransport A 𝒢 q)
    (κ : Type) [Field κ] [IsAlgClosed κ] [DecidableEq κ] [Algebra A κ] (hM'κ : ((M' : ℕ) : κ) ≠ 0)
    (x x' : (WeierstrassCurve.DrinfeldGlobal.rigidDataPow A ℓ' M' q hℓ hM 𝒢 𝒯).Raw κ)
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
      ((WeierstrassCurve.DrinfeldGlobal.rigidDataPow A ℓ' M' q hℓ hM 𝒢 𝒯).act C₀ x).curve = x'.curve ∧ ((WeierstrassCurve.DrinfeldGlobal.rigidDataPow A ℓ' M' q hℓ hM 𝒢 𝒯).act C₀ x).level.1 = x'.level.1 := by sorry
