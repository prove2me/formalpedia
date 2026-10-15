-- Prove2me | Theorems.Thm_VerticalOwnership_CheapTalk_eq_2
-- name    : VerticalOwnership.CheapTalk.eq_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:40:33.870289+00:00
-- url     : https://prove2.me/theorems/8108e011-e076-49cd-924f-52d8d78adf60
-- title:
--   (2), p. 8 — the supplier's expected profit is w(z_s K − ∫_{q^adv−μ_i}^{K−μ_i} F(x)dx) for K ≥ q^adv
-- statement:
--   In the model of the mission, let $i\in\{L,H\}$, let $q^{adv}$ be an advance order and $K\ge q^{adv}$ a capacity level. The supplier's expected profit $\pi_s(K\mid\mu_i,q^{adv})=\mathbb E[w\min(K,\max(\mu_i+\varepsilon,q^{adv}))-cK]$ satisfies
--   $$\pi_s(K\mid\mu_i,q^{adv})=w\Big(K-\int_{q^{adv}-\mu_i}^{K-\mu_i}F(x)\,dx\Big)-cK=w\Big(z_sK-\int_{q^{adv}-\mu_i}^{K-\mu_i}F(x)\,dx\Big),$$
--   where $F$ is the CDF of $\varepsilon$ and $z_s=1-c/w$.
--
--   This closed form turns every comparison of the supplier's payoffs into a statement about integrals of $F$.
--
--   **Formalization Note** The hypothesis $K\ge q^{adv}$ is the paper's standing requirement that the capacity covers the advance order (p. 7, "$K(\ge q^{adv})$"); the identity fails without it.
-- source:
--   Avinadav, Shamir, Partial Vertical Ownership, Capacity Investment and Information Exchange in a Supply Chain, author manuscript of 2022-06-06 (Management Science, doi:10.1287/mnsc.2023.4673), p. 8, (2); proof p. 42, Appendix E, Proof of equations (2)-(4)

import Mathlib
import Definitions.Def_VerticalOwnership_CheapTalk_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace VerticalOwnership.CheapTalk

theorem eq_2 (M : Model) (hM : M.Standing) (μ q K : ℝ) (hμ : μ = M.μL ∨ μ = M.μH)
    (hqK : q ≤ K) :
    M.πs μ q K = M.w * (K - ∫ x in q - μ..K - μ, cdf M.P x) - M.c * K ∧
    M.πs μ q K = M.w * (M.zs * K - ∫ x in q - μ..K - μ, cdf M.P x) := by sorry

end VerticalOwnership.CheapTalk
