-- Prove2me | Theorems.Thm_SubscriptionPlanning_GrandOptimal_lemma_3_claim_1
-- name    : SubscriptionPlanning.GrandOptimal.lemma_3_claim_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:03:14.251661+00:00
-- url     : https://prove2.me/theorems/411ed528-baf3-4693-bcfc-773245e296e9
-- title:
--   Proof of Lemma 3, Claim 1, p. 28 (PDF 29) — under Condition 2, a larger relative gain of the chosen set implies a weakly larger fee
-- statement:
--   Fix rental prices $\mathbf r \ge 0$ satisfying Condition 2, and a feasible subscription planning: fees $p$ with $p(\emptyset) = 0$ and sets $S_1, \dots, S_n$ satisfying the incentive constraints (3). For user types $i, i'$, if
--   $$\frac{\mathrm{SubGain}(i,S_i,\mathbf r)}{\mathrm{SubGain}(i,\mathcal M,\mathbf r)} \ge \frac{\mathrm{SubGain}(i',S_{i'},\mathbf r)}{\mathrm{SubGain}(i',\mathcal M,\mathbf r)},$$
--   then $p(S_i) \ge p(S_{i'})$.
--
--   Under Condition 2 all types rank sets by the same relative gain, so a type choosing a set with higher relative gain pays at least as much. This is the first half of the proof of Lemma 3.
--
--   **Formalization Note** A ratio with zero denominator is $0$ in Lean; the statement remains the paper's in that case because $\mathrm{SubGain}(i,\cdot,\mathbf r)$ then vanishes identically. Condition 2 is in its cross-multiplied form. The hypothesis $\mathbf r \ge 0$ is added.
-- source:
--   Alaei, Makhdoumi, Malekian, Optimal Subscription Planning for Digital Goods, working paper (SSRN 3476296; Operations Research, doi:10.1287/opre.2023.2468), p. 28, proof of Lemma 3, Claim 1

import Mathlib
import Definitions.Def_SubscriptionPlanning_GrandOptimal_Setting

namespace SubscriptionPlanning.GrandOptimal
theorem lemma_3_claim_1 {n m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (M : Model n m Ω)
    (hM : M.Valid) (r : Fin m → ℝ) (hr : ∀ j, 0 ≤ r j) (hC : Condition2 M r)
    (p : Finset (Fin m) → ℝ) (S : Fin n → Finset (Fin m)) (hF : IsFeasible M r p S)
    (i i' : Fin n) (hg : relGain M i' (S i') r ≤ relGain M i (S i) r) :
    p (S i') ≤ p (S i) := by sorry
end SubscriptionPlanning.GrandOptimal
