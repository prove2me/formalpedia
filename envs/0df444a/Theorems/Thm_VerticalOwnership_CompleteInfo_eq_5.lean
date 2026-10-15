-- Prove2me | Theorems.Thm_VerticalOwnership_CompleteInfo_eq_5
-- name    : VerticalOwnership.CompleteInfo.eq_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:40:28.218248+00:00
-- url     : https://prove2.me/theorems/fba05757-17c4-4151-8902-a45a924b7374
-- title:
--   (5), p. 10 — K_i^CI(q^adv) is the unique maximizer of the supplier's expected profit over capacities K ≥ q^adv
-- statement:
--   Let $\mu_i \in \{\mu_L, \mu_H\}$ and let $q^{adv} \ge 0$ be an advance order. Among capacities $K \ge q^{adv}$, the supplier's expected profit $K \mapsto \pi_s(K \mid \mu_i, q^{adv})$ is maximized exactly at
--   $$K_i^{CI}(q^{adv}) = \begin{cases} \mu_i + F^{-1}(z_s) & q^{adv} \le \mu_i + F^{-1}(z_s),\\ q^{adv} & \text{otherwise}, \end{cases}$$
--   that is: $K_i^{CI}(q^{adv}) \ge q^{adv}$, it attains the maximum, and every capacity $K \ge q^{adv}$ attaining the maximum equals $K_i^{CI}(q^{adv})$.
--
--   Equation (5) is the supplier's best response under complete information: the newsvendor capacity, raised to the advance order if the order exceeds it.
--
--   **Formalization Note** The paper states (5) as the supplier's choice; the theorem makes "optimal" explicit as unique maximization over $K \ge q^{adv}$.
-- source:
--   Avinadav, Shamir, Partial Vertical Ownership, Capacity Investment and Information Exchange in a Supply Chain, author manuscript of 2022-06-06 (Management Science, doi:10.1287/mnsc.2023.4673), p. 10, (5)

import Mathlib
import Definitions.Def_VerticalOwnership_CompleteInfo_Setting
open MeasureTheory ProbabilityTheory

namespace VerticalOwnership.CompleteInfo

theorem eq_5 (M : Model) (hM : M.Standing) (μ : ℝ) (hμ : μ ∈ ({M.μL, M.μH} : Set ℝ))
    (q : ℝ) (hq : 0 ≤ q) :
    q ≤ M.KCI μ q ∧
      IsMaxOn (fun K => M.πs μ q K) (Set.Ici q) (M.KCI μ q) ∧
      ∀ K, q ≤ K → M.πs μ q K = M.πs μ q (M.KCI μ q) → K = M.KCI μ q := by sorry

end VerticalOwnership.CompleteInfo
