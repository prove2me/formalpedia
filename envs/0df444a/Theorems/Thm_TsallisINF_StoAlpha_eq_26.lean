-- Prove2me | Theorems.Thm_TsallisINF_StoAlpha_eq_26
-- name    : TsallisINF.StoAlpha.eq_26
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:40:13.860058+00:00
-- url     : https://prove2.me/theorems/c14932b0-7f9a-445f-ae16-e4f993289c16
-- title:
--   (26), App. D p. 45 — the stability of α-Tsallis-INF with the parameters of Theorem 4
-- statement:
--   Let $K\ge2$, $\alpha\in(0,1)$ and $\Delta\in[0,1]^K$ with a unique zero $i^*$ ($\Delta_i>0$ for $i\ne i^*$), and $\Delta_{\min}=\min_{i\ne i^*}\Delta_i$. Run α-Tsallis-INF with importance-weighted estimators, learning rate $\eta_t=\frac{16^\alpha}{4}\frac{1-\bar t^{-1+\alpha}}{(1-\alpha)t^\alpha}$ ($\bar t=\max\{e,t\}$) and asymmetric regularizer $\xi_i=\Delta_i^{1-2\alpha}$ ($i\ne i^*$), $\xi_{i^*}=\Delta_{\min}^{1-2\alpha}$, against a randomized adaptive adversary with losses in $[0,1]$. With $T_0=\frac{16}{\Delta_{\min}^2}\log^2\frac{16}{\Delta_{\min}^2}$, for every $T\ge1$
--   $$\mathbb E\Big[\sum_{t=1}^T\ell_{t,I_t}+\Phi_t(-\hat L_t)-\Phi_t(-\hat L_{t-1})\Big]\le\sum_{i\ne i^*}\Big(\min\Big\{\frac1{1-\alpha},\log T\Big\}\frac{2(\log T+1)}{\Delta_i}+\sum_{t=1}^T\frac{\Delta_i\,\mathbb E[w_{t,i}]}{2}\Big)+\frac{4\log^4(T_0)}{\Delta_{\min}}.$$
--
--   This is the stability half of the proof of Theorem 4; the term $\sum_t\Delta_i\mathbb E[w_{t,i}]/2$ is later absorbed by the self-bounding property.
--
--   **Formalization Note** The statement needs no assumption on the environment beyond losses in $[0,1]$. Arms are `Fin K`; expectations use the law of the first $T$ rounds; $\log$ is natural.
-- source:
--   Zimmert & Seldin, Tsallis-INF: An Optimal Algorithm for Stochastic and Adversarial Bandits, arXiv:1807.07623v6, p. 45, display (26) (Appendix D, proof of Theorem 4)

import Mathlib
import Definitions.Def_TsallisINF_StoAlpha_Setting

open MeasureTheory

namespace TsallisINF.StoAlpha
theorem eq_26 {K : ℕ} (hK : 1 < K) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (adv : Ω → Adversary K)
    (hadv : ∀ t h i, Measurable (fun ω => (adv ω).val t h i))
    (α : ℝ) (hα : α ∈ Set.Ioo (0 : ℝ) 1) (Δ : Fin K → ℝ) (istar : Fin K)
    (hΔ : ∀ i, Δ i ∈ Set.Icc (0 : ℝ) 1) (hΔstar : Δ istar = 0)
    (hΔpos : ∀ i, i ≠ istar → 0 < Δ i)
    (W : ℕ → Ω → (ℕ → Fin K) → Fin K → ℝ)
    (hW : IsAlphaTsallisINF α (xiThm4 hK α Δ istar) (etaThm4 α) (estIW adv W) W)
    (T : ℕ) (hT : 1 ≤ T) :
    stability μ adv W ⟨0, by omega⟩ α (xiThm4 hK α Δ istar) (etaThm4 α) T ≤
      ∑ i ∈ Finset.univ.erase istar,
        (min (1 / (1 - α)) (Real.log T) * (2 * (Real.log T + 1)) / Δ i +
          ∑ t ∈ Finset.Icc 1 T, Δ i * meanW μ W ⟨0, by omega⟩ T t i / 2) +
        4 * Real.log (T0 hK Δ istar) ^ 4 / deltaMin hK Δ istar := by sorry
end TsallisINF.StoAlpha
