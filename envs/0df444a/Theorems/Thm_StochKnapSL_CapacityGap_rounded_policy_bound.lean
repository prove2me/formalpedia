-- Prove2me | Theorems.Thm_StochKnapSL_CapacityGap_rounded_policy_bound
-- name    : StochKnapSL.CapacityGap.rounded_policy_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:20:15.926457+00:00
-- url     : https://prove2.me/theorems/d77c7db8-8c5a-41c1-a09f-fb1339776a37
-- title:
--   Proof of Theorem 4, p. 37 — the rounded policy A′ satisfies E[Σ_{k∈U} d̃_k y^{A′}_k] ≥ Σ_{k∈U} E[d̃_k] α_k
-- statement:
--   Assume the standing assumptions of §3.3. Let $\pi = \sum_j w_j A_j$ be a randomized adaptive policy that, with capacity $Q$, fully serves every customer $i$ with probability at least $\alpha_i$. Let $A'_j$ be the policy obtained from $A_j$ by also serving in full the customer (if any) at which the run of $A_j$ stops for lack of capacity. Then $y^{A'_j}_k$, the indicator that $A'_j$ serves $k$, is the indicator that the run of $A_j$ reaches $k$. For every set $U$ of customers,
--   $$ \sum_{k\in U} \mathbf E[\tilde d_k]\, \alpha_k \le \sum_j w_j\, \mathbf E\Big[\sum_{k \in U} \tilde d_k\, y^{A'_j}_k\Big]. $$
--
--   The step uses that whether $k$ is reached depends only on the demands of the customers chosen before her, and so is independent of $\tilde d_k$. Together with the capacity bound for $A'$, it gives $\alpha \in \Gamma(Q + \Delta)$ in the proof of Theorem 4.
-- source:
--   Lyu, Chou, Teo, Zheng & Zhong, Stochastic Knapsack Revisited: The Service Level Perspective, SSRN working paper 3674463 (version of 2021-05-29), p. 37, proof of Theorem 4 (Appendix A.3)

import Mathlib
import Definitions.Def_StochKnapSL_CapacityGap_Model
open MeasureTheory ProbabilityTheory

namespace StochKnapSL.CapacityGap

/-- Proof of Theorem 4, p. 37: for a randomized adaptive policy meeting the Type-I targets with
capacity `Q`, the rounded-up policy `A'` (serve every customer the run reaches) satisfies
`E[∑_{k∈U} d_k y^{A'}_k] ≥ ∑_{k∈U} E[d_k] α_k` for every subset `U`. -/
theorem rounded_policy_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {N : ℕ} (d : Fin N → Ω → ℝ) (Δ : ℝ) (α : Fin N → ℝ)
    (hS : Standing μ d Δ α) (Q : ℝ) (π : Mixture (AdaptivePolicy N))
    (hπ : ∀ i, α i ≤ serviceProb μ d π Q i) (U : Finset (Fin N)) :
    ∑ k ∈ U, (∫ ω, d k ω ∂μ) * α k ≤
      ∑ j, π.w j * ∫ ω, ∑ k ∈ U,
        d k ω * (if reached (π.pol j) Q (fun l => d l ω) k then (1 : ℝ) else 0) ∂μ := by sorry

end StochKnapSL.CapacityGap
