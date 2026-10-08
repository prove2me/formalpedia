-- Prove2me | Theorems.Thm_TsallisINF_StoAlpha_eq_30
-- name    : TsallisINF.StoAlpha.eq_30
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:39:41.747988+00:00
-- url     : https://prove2.me/theorems/4c502754-f789-4e30-ab5a-86765b73e728
-- title:
--   (30), App. D p. 46 — the penalty of α-Tsallis-INF with the parameters of Theorem 4
-- statement:
--   In the setting of (26) — $K\ge2$, $\alpha\in(0,1)$, a gap vector $\Delta\in[0,1]^K$ with unique zero $i^*$, α-Tsallis-INF with IW estimators, $\eta_t=\frac{16^\alpha}{4}\frac{1-\bar t^{-1+\alpha}}{(1-\alpha)t^\alpha}$ and $\xi_i=\Delta_i^{1-2\alpha}$ ($i\ne i^*$), $\xi_{i^*}=\Delta_{\min}^{1-2\alpha}$ — let $T\ge1$ and assume that $i^*$ is a best arm in expectation in hindsight at horizon $T$. Then
--   $$\mathbb E\Big[\sum_{t=1}^T-\Phi_t(-\hat L_t)+\Phi_t(-\hat L_{t-1})-\ell_{t,i^*}\Big]\le\sum_{i\ne i^*}\Big(\frac{16(\log T+1)}{\Delta_i}+\sum_{t=1}^T\frac{\Delta_i\,\mathbb E[w_{t,i}]}{4}\Big)+1.$$
--
--   This is the penalty half of the proof of Theorem 4.
--
--   **Formalization Note** The page writes the penalty with $\ell_{t,i^*_T}$ and sums over $i\ne i^*$, i.e. it uses $i^*_T=i^*$, which holds in the stochastically constrained regime (p. 6); here that identity is the hypothesis that $i^*$ is a best arm in hindsight. The paper derives (30) from Lemma 12 (part 2), which assumes non-increasing learning rates; the rate of Theorem 4 is not monotone for small $\alpha$ (e.g. it increases from $t=3$ to $t=4$ at $\alpha=1/2$), and the statement is given as printed.
-- source:
--   Zimmert & Seldin, Tsallis-INF: An Optimal Algorithm for Stochastic and Adversarial Bandits, arXiv:1807.07623v6, p. 46, display (30) (Appendix D, proof of Theorem 4)

import Mathlib
import Definitions.Def_TsallisINF_StoAlpha_Setting

open MeasureTheory

namespace TsallisINF.StoAlpha
theorem eq_30 {K : ℕ} (hK : 1 < K) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (adv : Ω → Adversary K)
    (hadv : ∀ t h i, Measurable (fun ω => (adv ω).val t h i))
    (α : ℝ) (hα : α ∈ Set.Ioo (0 : ℝ) 1) (Δ : Fin K → ℝ) (istar : Fin K)
    (hΔ : ∀ i, Δ i ∈ Set.Icc (0 : ℝ) 1) (hΔstar : Δ istar = 0)
    (hΔpos : ∀ i, i ≠ istar → 0 < Δ i)
    (W : ℕ → Ω → (ℕ → Fin K) → Fin K → ℝ)
    (hW : IsAlphaTsallisINF α (xiThm4 hK α Δ istar) (etaThm4 α) (estIW adv W) W)
    (T : ℕ) (hT : 1 ≤ T)
    (hbest : IsBestInHindsight μ adv W ⟨0, by omega⟩ T istar) :
    penalty μ adv W ⟨0, by omega⟩ α (xiThm4 hK α Δ istar) (etaThm4 α) T istar ≤
      ∑ i ∈ Finset.univ.erase istar,
        (16 * (Real.log T + 1) / Δ i +
          ∑ t ∈ Finset.Icc 1 T, Δ i * meanW μ W ⟨0, by omega⟩ T t i / 4) + 1 := by sorry
end TsallisINF.StoAlpha
