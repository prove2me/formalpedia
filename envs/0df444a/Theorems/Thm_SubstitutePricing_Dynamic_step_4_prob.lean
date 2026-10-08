-- Prove2me | Theorems.Thm_SubstitutePricing_Dynamic_step_4_prob
-- name    : SubstitutePricing.Dynamic.step_4_prob
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:17:41.715756+00:00
-- url     : https://prove2.me/theorems/2cb54eb1-9d74-42da-a195-cc0af2c6a76e
-- title:
--   Step 4 — optimal choice-probability vector (19)–(20)
-- statement:
--   For a nonempty stocked set $S$, fixed marginal values $\delta_i$, and a margin $m$ satisfying (21), define
--
--   $$
--   p_0^*=\frac{\mu}{m},\qquad p_i^*=\frac{\mu}{m}\exp\left(\frac{a_i-\delta_i-u_0-m}{\mu}\right)\quad(i\in S).
--   $$
--
--   These coordinates form an interior choice-probability vector, maximize the marginal revenue in equation (8) over the positive choice simplex, and uniquely determine its maximizing coordinates on $S$ and the outside option. This identifies the probability vector from which the paper recovers optimal prices.
--
--   **Formalization Note** Coordinates outside $S$ are immaterial, so uniqueness is stated only for the active coordinates and outside option.
-- source:
--   Dong, Kouvelis, Tian, Dynamic Pricing and Inventory Control of Substitute Products, Manufacturing & Service Operations Management 11(2) (2009), pp. 335–336, Appendix A, proof of Theorem 1, Step 4, (19)–(21)

import Definitions.Def_SubstitutePricing_Dynamic_Model

namespace SubstitutePricing.Dynamic
/-- Step 4: (19)–(21) identify the unique maximizing choice probabilities. -/
theorem step_4_prob (M : Model) (hM : M.Assumptions)
    (S : Finset (Fin M.n)) (hS : S.Nonempty) (δ : Fin M.n → ℝ) (m : ℝ)
    (hm : (m / M.μ - 1) * Real.exp ((m + M.u0) / M.μ) =
      ∑ i ∈ S, Real.exp ((M.a i - δ i) / M.μ)) :
    let qstar : (Fin M.n → ℝ) × ℝ := (M.pstar δ m, M.μ / m)
    qstar ∈ M.choiceDomain S ∧
    (∀ q ∈ M.choiceDomain S, M.probObjective S δ q ≤ M.probObjective S δ qstar) ∧
    (∀ q ∈ M.choiceDomain S,
      M.probObjective S δ q = M.probObjective S δ qstar →
      q.2 = qstar.2 ∧ ∀ i ∈ S, q.1 i = qstar.1 i) := by sorry
end SubstitutePricing.Dynamic
