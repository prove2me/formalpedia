-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_inLine_level_snd_fst_xP_of_curve_eq_of_level_fst_eq_rigidDataH1Pow
-- name    : WeierstrassCurve.DrinfeldGlobal.inLine_level_snd_fst_xP_of_curve_eq_of_level_fst_eq_rigidDataH1Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/7d551abd-5671-5d6a-9952-d81c655208c4
-- title:
--   Two H₁-admissible Γ₁(ℓ_g)-points on one curve lie in line
-- statement:
--   Let $A$ be a commutative ring, let $\ell_g, M', q$ be natural numbers with $M'$ nonzero, and fix the three equivariance hypotheses used to build the moduli datum: $h_\ell$, that over every $A$-algebra $T$ the condition [`ModularCurve.IsGamma1Point`](def/ModularCurve_WeierstrassGamma1Pow.html#L10) for $\ell_g$ (the point $(x_P,y_P)$ lies on the affine curve, $\mathrm{pre}\Psi_{\ell_g}(x_P)=0$, and $(x_Q,y_Q)=(x_P,y_P)$) is preserved by a Weierstrass variable change $C$ acting on the curve and on the level-$p$ datum; $h_M$, that [`ModularCurve.IsGamma0PowAt`](def/ModularCurve_WeierstrassGamma0Pow.html#L55) for $(p,k)$ is preserved when $h$ is replaced by `kernelVariableChangeDeg` $C$ of degree $\mathrm{gamma0PowDeg}\,p\,k$; and $h_L$, that divisibility of `inLineMulPoly` $W\,\ell_g\,n\,x$ transports likewise. Let $\mathcal G$ be a family of relative group laws on Weierstrass projective models over $A$-algebras, $\mathcal T$ a level transport at $q$, and $\kappa$ an algebraically closed $A$-field with $M'\ne 0$ in $\kappa$. Assume $\ell_g$ is a prime, $\ell_g \ne 2$ and $\ell_g \mid M'$. Let $x, x'$ be raw $\kappa$-points of `rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯`: each a Weierstrass curve with unit discriminant, a family $h$ of kernel polynomials indexed by the prime factors of $M'$ satisfying `IsGamma0PowAt` at the corresponding exponent, a `LevelPData` satisfying `IsGamma1Point` for $\ell_g$, and a Drinfeld level-$q$ pair, subject to [`ModularCurve.IsGamma1Link`](def/ModularCurve_WeierstrassH1Pow.html#L26) $W\,\ell_g\,M'$ between the first two. If $x$ and $x'$ have the same curve and the same $\Gamma_0$-component $h$, then [`ModularCurve.InLine`](def/ModularCurve_KatzLevelP.html#L21) holds for $x'.\mathrm{curve}$, $\ell_g$ and the two abscissae: there is $a$ with $1 \le a \le (\ell_g-1)/2$ and $x_P \cdot \Psi_a^2(x_{P'}) = \Phi_a(x_{P'})$, where $x_P$, $x_{P'}$ are the $x$-coordinates of the $\Gamma_1(\ell_g)$-points of $x$ and $x'$.
--
--   This is the rigidity statement underlying the diamond action: on a fixed curve with a fixed cyclic $\Gamma_0(M')$-structure, two $H_1$-admissible $\Gamma_1(\ell_g)$-points have $x$-coordinates related by multiplication by some $a$ with $1 \le a \le (\ell_g-1)/2$, i.e. they differ by a diamond operator up to sign. It feeds the full-level comparison [`ModularCurve.FullLevel.Diamond.forall_nsmul_eq_zero_and_exists_variableChange_and_inLine_of_over_of_eq_map_classify_rigidDataH1Pow_of_tatePoint_pinGamma1`](thm.html#ModularCurve.FullLevel.Diamond.forall_nsmul_eq_zero_and_exists_variableChange_and_inLine_of_over_of_eq_map_classify_rigidDataH1Pow_of_tatePoint_pinGamma1).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_inLine_level_snd_fst_xP_of_curve_eq_of_level_fst_eq_rigidDataH1Pow.lean

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

theorem WeierstrassCurve.DrinfeldGlobal.inLine_level_snd_fst_xP_of_curve_eq_of_level_fst_eq_rigidDataH1Pow
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
    (hℓg : ℓg.Prime) (hℓg2 : ℓg ≠ 2) (hℓgM' : ℓg ∣ M')
    (x x' : (WeierstrassCurve.DrinfeldGlobal.rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).Raw κ)
    (hc : x.curve = x'.curve) (ht : x.level.1 = x'.level.1) :
    ModularCurve.InLine x'.curve ℓg x'.level.2.1.xP x.level.2.1.xP := by sorry
