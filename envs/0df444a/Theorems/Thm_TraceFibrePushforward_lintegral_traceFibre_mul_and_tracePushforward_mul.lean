-- Prove2me | Theorems.Thm_TraceFibrePushforward_lintegral_traceFibre_mul_and_tracePushforward_mul
-- name    : TraceFibrePushforward.lintegral_traceFibre_mul_and_tracePushforward_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/220d8f78-8ba3-5aa1-a646-41666043cf05
-- title:
--   Dilation law for trace fibres and the trace push-forward
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra, and let $a$ be a unit of the adele ring $\mathbb{A}_K$ of $K$; write $n = \mathrm{finrank}_K L$ and let $\beta =$ [`M4aHerbrand.Bridge.genuineβ K L`](def/M4aHerbrand_GenuineBeta.html#L14) denote the map from $\mathbb{A}_K$ to $\mathbb{A}_L$ used throughout. Recall that for $r \in \mathbb{A}_K$ and $w$ a tuple indexed by $\mathrm{Fin}(\mathrm{finrank}_K(\ker(\mathrm{Tr}_{L/K})))$ of elements of $\mathbb{A}_K$, the trace fibre point `traceFibre K L r w` is $\beta(r)\cdot (n)^{-1} + \sum_i \beta(w_i)\cdot e_i$, the scalars $(n)^{-1}$ and the members $e_i$ of the basis `Module.finBasis` of $\ker(\mathrm{Tr}_{L/K})$ being mapped into $\mathbb{A}_L$ by the structure map from $L$; and that `tracePushforward K L F r` is the Bochner integral over such tuples $w$ of $F(\mathrm{traceFibre}\,K\,L\,r\,w)$ against the product of copies of the additive Haar measure `adelicAddHaar` on $\mathbb{A}_K$ (taken for the Borel $\sigma$-algebra on the adeles). Set $\lVert a\rVert =$ [`NumberField.TateGlobal.ideleNorm K a`](def/NumberField_TateGlobalZeta.html#L19), the value at $a$ of the distributive Haar character of $\mathbb{A}_K$, viewed as a real number. The theorem asserts two things simultaneously. First, for every function $G : \mathbb{A}_L \to \overline{\mathbb{R}}_{\ge 0}$ and every $r \in \mathbb{A}_K$, the lower Lebesgue integral of $w \mapsto G(\beta(a)\cdot \mathrm{traceFibre}\,K\,L\,r\,w)$ against that product measure equals $\mathrm{ofReal}\big((\lVert a\rVert^{\,n-1})^{-1}\big)$ times the lower Lebesgue integral of $w \mapsto G(\mathrm{traceFibre}\,K\,L\,(a r)\,w)$, the exponent $n-1$ being truncated subtraction of naturals. Second, for every $F : \mathbb{A}_L \to \mathbb{C}$ and every $r \in \mathbb{A}_K$, one has `tracePushforward K L (fun x => F (β(a) * x)) r` $= (\lVert a\rVert^{\,n-1})^{-1}$, coerced to $\mathbb{C}$, times `tracePushforward K L F (a * r)`. No measurability or integrability hypothesis is imposed on $G$ or $F$.
--
--   This is the homogeneity (dilation) law describing how the fibration of $\mathbb{A}_L$ over $\mathbb{A}_K$ along the trace, and the push-forward of functions along it, transform when an idele of the base field acts: dilating by $a$ rescales fibre integrals by $\lVert a\rVert^{-(n-1)}$, the factor coming from the $(n-1)$-dimensional fibre direction. It is used in the twisted Bruhat computations, namely by [`AutomorphicForm.TwistedBruhat.unipotentFold_mul_idelesBaseChange_eq_mul_integral_finsum_tracePushforward_sub`](thm.html#AutomorphicForm.TwistedBruhat.unipotentFold_mul_idelesBaseChange_eq_mul_integral_finsum_tracePushforward_sub) and [`AutomorphicForm.TwistedBruhat.unipotentFold_mul_idelesBaseChange_map_algebraMap_eq`](thm.html#AutomorphicForm.TwistedBruhat.unipotentFold_mul_idelesBaseChange_map_algebraMap_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TraceFibrePushforward_lintegral_traceFibre_mul_and_tracePushforward_mul.lean

import Definitions.Def_AutomorphicForm_AdelicTracePushforward
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar
open AutomorphicForm.AdelicTracePushforward
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

theorem TraceFibrePushforward.lintegral_traceFibre_mul_and_tracePushforward_mul
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (a : (AdeleRing (𝓞 K) K)ˣ) :
    (∀ (G : AdeleRing (𝓞 L) L → ℝ≥0∞) (r : AdeleRing (𝓞 K) K),
      ∫⁻ w, G (M4aHerbrand.Bridge.genuineβ K L (a : AdeleRing (𝓞 K) K) * traceFibre K L r w)
          ∂(Measure.pi fun _ => adelicAddHaar (𝓞 K) K) =
        ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K a ^ (Module.finrank K L - 1))⁻¹) *
          ∫⁻ w, G (traceFibre K L ((a : AdeleRing (𝓞 K) K) * r) w) ∂(Measure.pi fun _ => adelicAddHaar (𝓞 K) K)) ∧
    (∀ (F : AdeleRing (𝓞 L) L → ℂ) (r : AdeleRing (𝓞 K) K),
      tracePushforward K L (fun x => F (M4aHerbrand.Bridge.genuineβ K L (a : AdeleRing (𝓞 K) K) * x)) r =
        (((NumberField.TateGlobal.ideleNorm K a ^ (Module.finrank K L - 1))⁻¹ : ℝ) : ℂ) *
          tracePushforward K L F ((a : AdeleRing (𝓞 K) K) * r)) := by sorry
