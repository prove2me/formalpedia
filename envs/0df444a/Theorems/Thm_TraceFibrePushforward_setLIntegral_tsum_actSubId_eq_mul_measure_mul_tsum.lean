-- Prove2me | Theorems.Thm_TraceFibrePushforward_setLIntegral_tsum_actSubId_eq_mul_measure_mul_tsum
-- name    : TraceFibrePushforward.setLIntegral_tsum_actSubId_eq_mul_measure_mul_tsum
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/aa2b8b61-2596-53aa-83c4-e22449f352f0
-- title:
--   Fundamental-domain lattice sums of σ-1 via the trace fibration
-- statement:
--   Let $K \subseteq L$ be number fields with $L/K$ Galois, let $\mu_K$ and $\mu_L$ be additive Haar measures on the adele rings $\mathbb{A}_K$ and $\mathbb{A}_L$, let $D$ be a Galois descent datum on the adeles of $L$ (a monoid homomorphism $\sigma \mapsto D.\mathrm{act}\,\sigma$ from $\mathrm{Gal}(L/K)$ to ring automorphisms of $\mathbb{A}_L$, compatible with the action on $L$ through $\mathrm{algebraMap}$ and continuous in each $\sigma$), let $\sigma$ be an element of $\mathrm{Gal}(L/K)$ with the property that every $\tau$ lies in the subgroup of integer powers of $\sigma$, and let $c \in [0,\infty]$ satisfy the disintegration identity $\int^- G \, d\mu_L = c \int^-_r \int^-_w G(\mathrm{traceFibre}\,K\,L\,r\,w)$ for all measurable $G : \mathbb{A}_L \to [0,\infty]$, the inner integral being over the product of $\dim_K \ker(\mathrm{Tr}_{L/K})$ copies of `adelicAddHaar` and the outer one over $\mu_K$; here $\mathrm{traceFibre}\,K\,L\,r\,w = \mathrm{genuine}\beta(r)\cdot [L:K]^{-1} + \sum_i \mathrm{genuine}\beta(w_i)\cdot e_i$ with $(e_i)$ the chosen $K$-basis of $\ker(\mathrm{Tr}_{L/K})$ and $\mathrm{genuine}\beta$ the adelic base-change map. Two assertions are made, each for every additive fundamental domain $X \subseteq \mathbb{A}_L$ for the principal subgroup $L$ with respect to $\mu_L$ and every additive fundamental domain $X_K \subseteq \mathbb{A}_K$ for the principal subgroup $K$ with respect to $\mu_K$. First, for every measurable $G : \mathbb{A}_L \to [0,\infty]$, $$\int^-_{X} \sum_{b \in L}{}' G\bigl(b + D.\mathrm{act}\,\sigma(x) - x\bigr) d\mu_L(x) = c\,\mu_K(X_K) \sum_{r \in K}{}' \int^-_w G(\mathrm{traceFibre}\,K\,L\,r\,w).$$ Second, for every measurable $F : \mathbb{A}_L \to \mathbb{C}$ such that the corresponding integral over $X$ of $\sum_{b \in L} \|F(b + D.\mathrm{act}\,\sigma(x) - x)\|$ is finite, $\int_X \sum_{b \in L} F(b + D.\mathrm{act}\,\sigma(x) - x)\, d\mu_L = (c\,\mu_K(X_K))^{\mathbb{R}} \sum_{r \in K} (\mathrm{tracePushforward}\,K\,L\,F)(r)$, where the scalar is the real number underlying $c\,\mu_K(X_K)$, the sums over $K$ and $L$ are over principal adeles, and $\mathrm{tracePushforward}\,K\,L\,F\,(r) = \int F(\mathrm{traceFibre}\,K\,L\,r\,w)\,dw$.
--
--   This is the unipotent-merge identity: a periodic sum over the lattice $L \subseteq \mathbb{A}_L$ precomposed with $\sigma - 1$, integrated over a fundamental domain, is re-expressed through the fibration of $\mathbb{A}_L$ over $\mathbb{A}_K$ coming from the trace form, turning it into a lattice sum over $K$ of the trace push-forward. It is used in the twisted Bruhat computation, by [`AutomorphicForm.TwistedBruhat.integrableOn_and_setIntegral_finsum_trace_ne_zero_unipotentMerge_eq_mul_finsum_tracePushforward`](thm.html#AutomorphicForm.TwistedBruhat.integrableOn_and_setIntegral_finsum_trace_ne_zero_unipotentMerge_eq_mul_finsum_tracePushforward).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TraceFibrePushforward_setLIntegral_tsum_actSubId_eq_mul_measure_mul_tsum.lean

import Definitions.Def_AutomorphicForm_AdelicTracePushforward

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar
open AutomorphicForm.AdelicTracePushforward
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

theorem TraceFibrePushforward.setLIntegral_tsum_actSubId_eq_mul_measure_mul_tsum
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (μK : Measure (AdeleRing (𝓞 K) K)) [μK.IsAddHaarMeasure]
    (μL : Measure (AdeleRing (𝓞 L) L)) [μL.IsAddHaarMeasure]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (c : ℝ≥0∞)
    (hc : ∀ G : AdeleRing (𝓞 L) L → ℝ≥0∞, Measurable G →
      ∫⁻ x, G x ∂μL = c * ∫⁻ r, ∫⁻ w, G (traceFibre K L r w) ∂(Measure.pi fun _ => adelicAddHaar (𝓞 K) K) ∂μK) :
    (∀ (X : Set (AdeleRing (𝓞 L) L)), IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 L) L) X μL →
      ∀ (XK : Set (AdeleRing (𝓞 K) K)), IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 K) K) XK μK →
      ∀ G : AdeleRing (𝓞 L) L → ℝ≥0∞, Measurable G →
        ∫⁻ x in X, ∑' b : L, G (algebraMap L (AdeleRing (𝓞 L) L) b + actSubId K L D σ x) ∂μL =
          c * μK XK * ∑' r : K, ∫⁻ w, G (traceFibre K L (algebraMap K (AdeleRing (𝓞 K) K) r) w)
            ∂(Measure.pi fun _ => adelicAddHaar (𝓞 K) K)) ∧
    (∀ (X : Set (AdeleRing (𝓞 L) L)), IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 L) L) X μL →
      ∀ (XK : Set (AdeleRing (𝓞 K) K)), IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 K) K) XK μK →
      ∀ F : AdeleRing (𝓞 L) L → ℂ, Measurable F →
        (∫⁻ x in X, ∑' b : L, ‖F (algebraMap L (AdeleRing (𝓞 L) L) b + actSubId K L D σ x)‖ₑ ∂μL ≠ ∞) →
        ∫ x in X, ∑' b : L, F (algebraMap L (AdeleRing (𝓞 L) L) b + actSubId K L D σ x) ∂μL =
          ((c * μK XK).toReal : ℂ) * ∑' r : K, tracePushforward K L F (algebraMap K (AdeleRing (𝓞 K) K) r)) := by sorry
