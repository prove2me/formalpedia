-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_rigidDataH1Pow_raw_eq_act_of_curve_eq_of_level_eq_of_pair_eq_one
-- name    : WeierstrassCurve.DrinfeldGlobal.rigidDataH1Pow_raw_eq_act_of_curve_eq_of_level_eq_of_pair_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/7e2d19bc-3cbf-5c97-a14e-3d68d3c28686
-- title:
--   Rigidity of raw H₁-data with origin Drinfeld pairs
-- statement:
--   Let $A$ be a commutative ring, let $\ell_g, M', q$ be natural numbers, and fix the three compatibility rules used to assemble the moduli datum: $h_\ell$, saying that a $\Gamma_1(\ell_g)$-point datum $D$ (a quadruple $x_P,y_P,x_Q,y_Q$ satisfying the affine equation of $W$, $(\mathrm{pre}\Psi_{\ell_g})(x_P)=0$, $x_Q=x_P$, $y_Q=y_P$) transforms to such a datum for $C\bullet W$ under `LevelPData.variableChange`; $h_M$, saying that `IsGamma0PowAt` is preserved by `kernelVariableChangeDeg`; and $h_L$, saying that divisibility of `inLineMulPoly` is preserved by the same substitution. Let $\mathcal G$ be a family of relative group laws on the projective models of curves with unit discriminant, assumed chord–tangent ($h\mathcal G$) and with identity section pinned at the origin chart ($h\mathcal G O$), let $\mathcal T$ be a level transport of raw Drinfeld pairs satisfying the section-transport property $h\mathcal T$, and let $h_{VC}$ provide variable-change graded homomorphisms. Let $T$ be an $A$-algebra and $x,x'$ raw points of `rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯` over $T$, $C$ a change of variables over $T$. Assume the curve, the $M'$-indexed family of kernel polynomials and the $\Gamma_1(\ell_g)$-point datum of $x'$ agree with those of $C$ acting on $x$, and that the Drinfeld pairs of $x$ and of $x'$ both have $P$ and $Q$ equal to the identity section of the associated group law. Then $x'$ equals $C$ acting on $x$. The proof uses neither $h\mathcal G$ nor $h_{VC}$.
--
--   This is the rigidity step for the origin slot of the $H_1$-type level structure: a raw point whose Drinfeld pair is the trivial pair is determined, among raw points, by its curve and its étale level data up to a prescribed change of variables. It feeds the analysis of automorphisms of the full-level moduli problem, being used in the Diamond-type comparison of $q$-expansions on full-level modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_rigidDataH1Pow_raw_eq_act_of_curve_eq_of_level_eq_of_pair_eq_one.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_ModularCurve_WeierstrassGamma1Pow
import Definitions.Def_ModularCurve_WeierstrassH1Pow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel

theorem WeierstrassCurve.DrinfeldGlobal.rigidDataH1Pow_raw_eq_act_of_curve_eq_of_level_eq_of_pair_eq_one
    (A : Type) [CommRing A] (ℓg M' q : ℕ)
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
    (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (𝒯 : LevelTransport A 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)
    (hVC : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve.Projective T) (C : WeierstrassCurve.VariableChange T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (C • W))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W)) ≤ (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsVariableChangeHom W C φ)
    (T : Type) [CommRing T] [Algebra A T]
    (x x' : (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).Raw T) (C : WeierstrassCurve.VariableChange T)

    (hcurve : x'.curve = ((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).act C x).curve)
    (htuple : x'.level.1 = ((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).act C x).level.1)
    (hgamma1 : x'.level.2.1 = ((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).act C x).level.2.1)

    (hx : ∃ hΔ : IsUnit x.level.2.2.curve.Δ,
      x.level.2.2.P = (𝒢 T x.level.2.2.curve hΔ).one (𝟙 _) ∧ x.level.2.2.Q = (𝒢 T x.level.2.2.curve hΔ).one (𝟙 _))
    (hx' : ∃ hΔ : IsUnit x'.level.2.2.curve.Δ,
      x'.level.2.2.P = (𝒢 T x'.level.2.2.curve hΔ).one (𝟙 _) ∧ x'.level.2.2.Q = (𝒢 T x'.level.2.2.curve hΔ).one (𝟙 _)) :
    x' = (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).act C x := by sorry
