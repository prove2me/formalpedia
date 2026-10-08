-- Prove2me | Theorems.Thm_TsallisINF_StoAlpha_theorem_4
-- name    : TsallisINF.StoAlpha.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:41:27.543056+00:00
-- url     : https://prove2.me/theorems/1af7f5cf-ecf9-443f-815c-45b5da36c8cc
-- title:
--   Theorem 4, p. 12 — α-Tsallis-INF with gap-tuned asymmetric regularization has logarithmic pseudo-regret in the stochastically constrained regime with a unique best arm
-- statement:
--   Let $K\ge2$ arms, $\alpha\in(0,1)$, and a gap vector $\Delta\in[0,1]^K$ with a unique zero $i^*$: $\Delta_{i^*}=0$ and $\Delta_i>0$ for $i\ne i^*$; let $\Delta_{\min}=\min_{i\ne i^*}\Delta_i$. Run α-Tsallis-INF with importance-weighted loss estimators, learning rate
--   $$\eta_t=\frac{16^\alpha}{4}\,\frac{1-\bar t^{-1+\alpha}}{(1-\alpha)t^\alpha},\qquad\bar t=\max\{e,t\},$$
--   and asymmetric regularizer with $\xi_i=\Delta_i^{1-2\alpha}$ for $i\ne i^*$ and $\xi_{i^*}=\Delta_{\min}^{1-2\alpha}$, against a randomized adaptive adversary with losses in $[0,1]$. Let $T\ge1$ and suppose that, as in every stochastically constrained adversarial regime with gaps $\Delta$ and unique best arm $i^*$ (§2, p. 6),
--   1. the pseudo-regret satisfies the self-bounding property with $C=0$: $\overline{Reg}_T\ge\mathbb E\big[\sum_{t=1}^T\sum_{i\ne i^*}w_{t,i}\Delta_i\big]$, and
--   2. $i^*$ is a best arm in expectation in hindsight at horizon $T$ ($i^*_T=i^*$).
--
--   Then
--   $$\overline{Reg}_T\le\sum_{i\ne i^*}\frac{\big(8\min\{\frac1{1-\alpha},\log T\}+64\big)(\log T+1)}{\Delta_i}+\frac{16\log^4\!\big(\frac{16}{\Delta_{\min}^2}\log^2\frac{16}{\Delta_{\min}^2}\big)}{\Delta_{\min}}+4.$$
--
--   The theorem shows that α-Tsallis-INF, tuned with knowledge of the gaps, attains logarithmic pseudo-regret in stochastically constrained environments for every $\alpha\in(0,1)$, not only for the gap-free choice $\alpha=1/2$ of Theorem 1.
--
--   **Formalization Note** The paper's hypothesis "any stochastically constrained adversarial regime with a unique best arm" requires conditional expectations given the past to state; its proof (Appendix D) uses only the two consequences derived on p. 6 and listed above, which every such regime satisfies, so the Lean statement is at least as strong as the printed one. The printed bound has $\log T$ in the first numerator; the proof (p. 47) ends with $(\log T+1)$, the constant stated here. The page allows $\alpha\in[0,1]$ with limit learning rates at the endpoints; the Lean statement takes $\alpha\in(0,1)$. Arms are `Fin K` (index base 0); $K\ge2$ makes $\Delta_{\min}$ well defined.
-- source:
--   Zimmert & Seldin, Tsallis-INF: An Optimal Algorithm for Stochastic and Adversarial Bandits, arXiv:1807.07623v6, p. 12, Theorem 4 (regime: §2, p. 6; constant: proof in Appendix D, p. 47)

import Mathlib
import Definitions.Def_TsallisINF_StoAlpha_Setting

open MeasureTheory

namespace TsallisINF.StoAlpha
theorem theorem_4 {K : ℕ} (hK : 1 < K) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (adv : Ω → Adversary K)
    (hadv : ∀ t h i, Measurable (fun ω => (adv ω).val t h i))
    (α : ℝ) (hα : α ∈ Set.Ioo (0 : ℝ) 1) (Δ : Fin K → ℝ) (istar : Fin K)
    (hΔ : ∀ i, Δ i ∈ Set.Icc (0 : ℝ) 1) (hΔstar : Δ istar = 0)
    (hΔpos : ∀ i, i ≠ istar → 0 < Δ i)
    (W : ℕ → Ω → (ℕ → Fin K) → Fin K → ℝ)
    (hW : IsAlphaTsallisINF α (xiThm4 hK α Δ istar) (etaThm4 α) (estIW adv W) W)
    (T : ℕ) (hT : 1 ≤ T)
    (hSB : SelfBounding μ adv W ⟨0, by omega⟩ T Δ istar 0)
    (hbest : IsBestInHindsight μ adv W ⟨0, by omega⟩ T istar) :
    pseudoRegret μ adv W ⟨0, by omega⟩ T ≤
      ∑ i ∈ Finset.univ.erase istar,
        (8 * min (1 / (1 - α)) (Real.log T) + 64) * (Real.log T + 1) / Δ i +
        16 * Real.log (T0 hK Δ istar) ^ 4 / deltaMin hK Δ istar + 4 := by sorry
end TsallisINF.StoAlpha
