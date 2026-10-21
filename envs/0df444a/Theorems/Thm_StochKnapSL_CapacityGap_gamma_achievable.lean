-- Prove2me | Theorems.Thm_StochKnapSL_CapacityGap_gamma_achievable
-- name    : StochKnapSL.CapacityGap.gamma_achievable
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:20:21.260259+00:00
-- url     : https://prove2.me/theorems/a6346b33-63c1-4fb7-9112-feea8994cb05
-- title:
--   p. 21 (Zhong et al. 2018) — every α ∈ Γ(Q) is attained in fill rate by a randomized priority policy
-- statement:
--   Let $\tilde d_1, \dots, \tilde d_N$ be integrable, almost surely non-negative random demands, let $Q \ge 0$, and let $\alpha \in \mathbb R^N_{\ge 0}$ lie in the polymatroid
--   $$ \Gamma(Q) = \Big\{ \alpha : \sum_{i\in U} \alpha_i \mathbf E[\tilde d_i] \le \mathbf E\Big[\min\Big(Q, \sum_{i \in U}\tilde d_i\Big)\Big]\ \ \forall U \subseteq \{1,\dots,N\}\Big\}. $$
--   Then there are priority orders $\sigma_1, \dots, \sigma_m$ and weights $w_k \ge 0$ with $\sum_k w_k = 1$ such that, writing $x^*_i(\sigma, \tilde d, Q)$ for the amount the greedy fractional fill in order $\sigma$ gives customer $i$,
--   $$ \alpha_i\, \mathbf E[\tilde d_i] \le \sum_{k=1}^m w_k\, \mathbf E\big[x^*_i(\sigma_k, \tilde d, Q)\big] \qquad \text{for every } i. $$
--   In words, a demand-independent randomization over priority orders attains fill rate at least $\alpha_i$ for every customer in the fractional (Type-II) system.
--
--   This is the achievability half of the characterization of Type-II service levels. The proof of Theorem 3 applies it at the capacity $Q_{II}$.
--
--   **Formalization Note.** Independence and the upper bound $\Delta$ are not needed and are not assumed. The paper cites this result from Zhong et al. (2018).
-- source:
--   Lyu, Chou, Teo, Zheng & Zhong, Stochastic Knapsack Revisited: The Service Level Perspective, SSRN working paper 3674463 (version of 2021-05-29), p. 21, §4.1 (citing Zhong et al. 2018); also p. 17

import Mathlib
import Definitions.Def_StochKnapSL_CapacityGap_Model
open MeasureTheory ProbabilityTheory

namespace StochKnapSL.CapacityGap

/-- p. 21 (citing Zhong et al. 2018): every `α ∈ Γ(Q)` is attained in fill rate by a randomized
anticipative (priority) policy in the fractional (Type-II) system. -/
theorem gamma_achievable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {N : ℕ} (d : Fin N → Ω → ℝ) (α : Fin N → ℝ) (Q : ℝ)
    (hmeas : ∀ i, Measurable (d i)) (hint : ∀ i, Integrable (d i) μ)
    (hnn : ∀ i, ∀ᵐ ω ∂μ, 0 ≤ d i ω) (hα : ∀ i, 0 ≤ α i) (hQ : 0 ≤ Q)
    (hΓ : InGamma μ d α Q) :
    ∃ π : Mixture (Equiv.Perm (Fin N)), ∀ i,
      α i * ∫ ω, d i ω ∂μ ≤ ∑ k, π.w k * ∫ ω, fill (π.pol k) Q (fun j => d j ω) i ∂μ := by sorry

end StochKnapSL.CapacityGap
