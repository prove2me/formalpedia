-- Prove2me | Theorems.Thm_TsallisINF_StoAlpha_lemma_20
-- name    : TsallisINF.StoAlpha.lemma_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:39:51.353546+00:00
-- url     : https://prove2.me/theorems/32bc54b2-128d-43ce-9a5f-c8b2777d0ab6
-- title:
--   Lemma 20, p. 41 — the penalty of α-Tsallis-INF is bounded by regularizer differences at any fixed $u,v\in\Delta^{K-1}$
-- statement:
--   Run α-Tsallis-INF with $\alpha\in(0,1)$, regularization parameters $\xi_i>0$, positive learning rates $\eta_1,\eta_2,\dots$ and any causal, measurable, integrable unbiased loss estimator against a randomized adaptive adversary with losses in $[0,1]$. Let $T\ge1$, let $i^*_T$ be a best arm in expectation in hindsight, and let $u,v\in\Delta^{K-1}$ be fixed. Writing $L_T=\sum_{t=1}^T\ell_t$ and $\Psi$ for the regularizer without learning rate,
--   $$\mathbb E\Big[\sum_{t=1}^T\Phi_t(-\hat L_{t-1})-\Phi_t(-\hat L_t)-\ell_{t,i^*_T}\Big]\le\mathbb E\Big[\frac{\Psi(v)-\Psi(w_1)}{\eta_1}+\sum_{t=2}^T\big(\eta_t^{-1}-\eta_{t-1}^{-1}\big)\big(\Psi(v)-\Psi(w_t)\big)+\frac{\Psi(u)-\Psi(v)}{\eta_T}+\big\langle u-e_{i^*_T},L_T\big\rangle\Big].$$
--
--   This is the standard telescoping bound on the penalty of follow-the-regularized-leader; both parts of Lemma 12 are derived from it by choosing $u$ and $v$.
--
--   **Formalization Note** The page writes $\langle u-e_{i^*_T},L_T\rangle$ outside the expectation; under an adaptive or randomized adversary $L_T$ is random, so it is placed inside (the two agree for an oblivious deterministic adversary). The page allows $\alpha\in[0,1]$; the Lean statement takes $\alpha\in(0,1)$. The estimator's causality, measurability, integrability and unbiasedness spell out the bandit protocol's standing assumptions.
-- source:
--   Zimmert & Seldin, Tsallis-INF: An Optimal Algorithm for Stochastic and Adversarial Bandits, arXiv:1807.07623v6, p. 41, Lemma 20

import Mathlib
import Definitions.Def_TsallisINF_StoAlpha_Setting

open MeasureTheory

namespace TsallisINF.StoAlpha
theorem lemma_20 {K : ℕ} (hK : 0 < K) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (adv : Ω → Adversary K)
    (hadv : ∀ t h i, Measurable (fun ω => (adv ω).val t h i))
    (α : ℝ) (hα : α ∈ Set.Ioo (0 : ℝ) 1) (ξ : Fin K → ℝ) (hξ : ∀ i, 0 < ξ i)
    (η : ℕ → ℝ) (hη : ∀ s, 1 ≤ s → 0 < η s)
    (W : ℕ → Ω → (ℕ → Fin K) → Fin K → ℝ)
    (est : ℕ → Ω → (ℕ → Fin K) → Fin K → ℝ)
    (hest : TsallisINF.Half.IsUnbiased μ adv W ⟨0, hK⟩ est)
    (hcausal : IsCausalEstimator est)
    (hW : IsAlphaTsallisINF α ξ η est W) (T : ℕ) (hT : 1 ≤ T)
    (istarT : Fin K) (hbest : IsBestInHindsight μ adv W ⟨0, hK⟩ T istarT)
    (u v : Fin K → ℝ) (hu : u ∈ stdSimplex ℝ (Fin K)) (hv : v ∈ stdSimplex ℝ (Fin K)) :
    penaltyWith μ adv W ⟨0, hK⟩ α ξ η est T istarT ≤
      TsallisINF.Half.expect μ W ⟨0, hK⟩ T (fun ω h =>
        (TsallisINF.AdvAlpha.tsallisPsi α ξ v - TsallisINF.AdvAlpha.tsallisPsi α ξ (W 1 ω h)) / η 1 +
          ∑ t ∈ Finset.Icc 2 T,
            ((η t)⁻¹ - (η (t - 1))⁻¹) * (TsallisINF.AdvAlpha.tsallisPsi α ξ v - TsallisINF.AdvAlpha.tsallisPsi α ξ (W t ω h)) +
          (TsallisINF.AdvAlpha.tsallisPsi α ξ u - TsallisINF.AdvAlpha.tsallisPsi α ξ v) / η T +
          ∑ t ∈ Finset.Icc 1 T,
            ((∑ i, u i * (adv ω).val t h i) - (adv ω).val t h istarT)) := by sorry
end TsallisINF.StoAlpha
