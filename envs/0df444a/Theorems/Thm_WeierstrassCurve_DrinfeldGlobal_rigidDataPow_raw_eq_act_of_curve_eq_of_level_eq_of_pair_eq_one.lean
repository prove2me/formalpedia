-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_rigidDataPow_raw_eq_act_of_curve_eq_of_level_eq_of_pair_eq_one
-- name    : WeierstrassCurve.DrinfeldGlobal.rigidDataPow_raw_eq_act_of_curve_eq_of_level_eq_of_pair_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/db9ad144-80ad-5616-8c67-ebee8a46105a
-- title:
--   Raw points with origin pairs and equal étale parts coincide
-- statement:
--   Fix a commutative ring $A$, natural numbers $\ell, M', q$, and the data entering `rigidDataPow`: a rule $h_\ell$ turning a level-$\ell$ Katz structure $D = (x_P,y_P,x_Q,y_Q)$ on a Weierstrass curve $W$ over an $A$-algebra into one on $C \bullet W$ via `LevelPData.variableChange`, a rule $h_M$ transporting the predicate `IsGamma0PowAt W p k h` to `IsGamma0PowAt (C • W) p k` of `kernelVariableChangeDeg C (gamma0PowDeg p k) h`, a family $\mathcal{G}$ of relative group laws on the graded projective models of curves with unit discriminant, the hypotheses that $\mathcal{G}$ is chord-tangent (each law admits a points evaluation compatible with addition and Galois twisting) and origin-identity (each identity section $\mathcal{G}_T(W,h_\Delta).\mathrm{one}$ is cut out by a ring homomorphism from the chart at the origin killing `xOverY` and `zOverY`), a level transport $\mathcal{T}$ for raw Drinfeld pairs together with the section-transport property, and the hypothesis $h_{VC}$ that every variable change is realised by a graded ring homomorphism of projective models satisfying `IsVariableChangeHom`. Let $T$ be an $A$-algebra and let $x, x'$ be raw points of `rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯` over $T$, that is, Weierstrass curves with unit discriminant carrying a triple consisting of a family of $\Gamma_0$-kernel polynomials indexed by the prime factors of $M'$, a level-$\ell$ Katz datum, and a raw Drinfeld pair, each satisfying its level condition. Let $C$ be a variable change over $T$, and assume that the curve of $x'$, its kernel-polynomial family and its Katz datum agree with those of $C$ acting on $x$; assume moreover that in both $x$ and $x'$ the Drinfeld pair is the origin pair, i.e. for some witness that the discriminant of the pair's curve is a unit both sections $P$ and $Q$ equal the identity section of the corresponding group law. Then $x' =$ the action of $C$ on $x$.
--
--   This is the rigidity step which says that, once the étale part (curve, $\Gamma_0(M')$-tuple, level-$\ell$ Katz datum) of a raw point is prescribed by a change of variables and the Drinfeld $\Gamma(q)$-pairs on both sides are the trivial pair $(O,O)$, the two raw points are literally related by that change of variables. It is used in the study of the full-level moduli ring at points where the only Drinfeld basis available is the origin pair, in [`ModularCurve.FullLevel.eq_of_isMaximal_of_mem_ssJSet_of_forall_coe_eq_qExpand_iff_chartAlgFin`](thm.html#ModularCurve.FullLevel.eq_of_isMaximal_of_mem_ssJSet_of_forall_coe_eq_qExpand_iff_chartAlgFin).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_rigidDataPow_raw_eq_act_of_curve_eq_of_level_eq_of_pair_eq_one.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel

theorem WeierstrassCurve.DrinfeldGlobal.rigidDataPow_raw_eq_act_of_curve_eq_of_level_eq_of_pair_eq_one
    (A : Type) [CommRing A] (ℓ M' q : ℕ)
    (hℓ : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ D →
        ModularCurve.IsLevelPStructure (C • W) ℓ (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (𝒯 : LevelTransport A 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)
    (hVC : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve.Projective T) (C : WeierstrassCurve.VariableChange T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (C • W))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W)) ≤ (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsVariableChangeHom W C φ)
    (T : Type) [CommRing T] [Algebra A T]
    (x x' : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).Raw T) (C : WeierstrassCurve.VariableChange T)

    (hcurve : x'.curve = ((rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).act C x).curve)
    (htuple : x'.level.1 = ((rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).act C x).level.1)
    (hkatz : x'.level.2.1 = ((rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).act C x).level.2.1)

    (hx : ∃ hΔ : IsUnit x.level.2.2.curve.Δ,
      x.level.2.2.P = (𝒢 T x.level.2.2.curve hΔ).one (𝟙 _) ∧ x.level.2.2.Q = (𝒢 T x.level.2.2.curve hΔ).one (𝟙 _))
    (hx' : ∃ hΔ : IsUnit x'.level.2.2.curve.Δ,
      x'.level.2.2.P = (𝒢 T x'.level.2.2.curve hΔ).one (𝟙 _) ∧ x'.level.2.2.Q = (𝒢 T x'.level.2.2.curve hΔ).one (𝟙 _)) :
    x' = (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).act C x := by sorry
