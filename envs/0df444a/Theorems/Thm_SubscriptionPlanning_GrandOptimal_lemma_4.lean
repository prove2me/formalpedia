-- Prove2me | Theorems.Thm_SubscriptionPlanning_GrandOptimal_lemma_4
-- name    : SubscriptionPlanning.GrandOptimal.lemma_4
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-10-22T23:03:11.941641+00:00
-- url     : https://prove2.me/theorems/8556b392-d7f2-4ee2-8159-f20318d69ae9
-- title:
--   Lemma 4, p. 13 (PDF 14), with q_i > 0 and the factor T of (3) — at an optimum each type is indifferent to the next lower type's set
-- statement:
--   Fix rental prices $\mathbf r \ge 0$ satisfying Condition 2, and suppose every user type has positive mass $q_i > 0$ and the types are ordered so that
--   $$\lambda_1\,\mathrm{SubGain}(1,\mathcal M,\mathbf r) \le \dots \le \lambda_n\,\mathrm{SubGain}(n,\mathcal M,\mathbf r).$$
--   Let $(p, S^*_1, \dots, S^*_n)$ be an optimal subscription planning: feasible (incentive constraints (3), $p(\emptyset) = 0$), with revenue at least that of every feasible planning. Then for every $i = 2, \dots, n$,
--   $$\lambda_i T\,\mathrm{SubGain}(i,S^*_i,\mathbf r) - p(S^*_i) = \lambda_i T\,\mathrm{SubGain}(i,S^*_{i-1},\mathbf r) - p(S^*_{i-1}).$$
--
--   At the optimum every downward incentive constraint between neighbouring types binds, which pins the fees down by the subscription gains.
--
--   **Formalization Note** The page writes $\lambda_i$ without the horizon $T$; the constraint (3) carries $\lambda_i T$, and the equality is stated with $\lambda_i T$ (it is false without $T$ when $T \ne 1$). The ordering is the paper's "without loss of generality" assumption. The hypothesis $q_i > 0$ is added: a type of mass zero contributes nothing to revenue, so an optimum may leave its constraint slack. The hypothesis $\mathbf r \ge 0$ is added.
-- source:
--   Alaei, Makhdoumi, Malekian, Optimal Subscription Planning for Digital Goods, working paper (SSRN 3476296; Operations Research, doi:10.1287/opre.2023.2468), p. 13, Lemma 4 (proof pp. 30–32)

import Mathlib
import Definitions.Def_SubscriptionPlanning_GrandOptimal_Setting

namespace SubscriptionPlanning.GrandOptimal
theorem lemma_4 {n m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (M : Model n m Ω)
    (hM : M.Valid) (hq : ∀ i, 0 < M.q i) (r : Fin m → ℝ) (hr : ∀ j, 0 ≤ r j)
    (hC : Condition2 M r) (p : Finset (Fin m) → ℝ) (S : Fin n → Finset (Fin m))
    (hopt : IsOptimal M r p S)
    (hsort : Monotone (fun i : Fin n => M.lam i * subGain M i Finset.univ r))
    (i : Fin n) (hi : 0 < i.val) :
    M.lam i * M.T * subGain M i (S i) r - p (S i) =
      M.lam i * M.T * subGain M i (S ⟨i.val - 1, by omega⟩) r - p (S ⟨i.val - 1, by omega⟩) := by sorry
end SubscriptionPlanning.GrandOptimal
