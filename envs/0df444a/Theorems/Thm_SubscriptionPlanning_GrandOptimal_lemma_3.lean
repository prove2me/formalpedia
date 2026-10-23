-- Prove2me | Theorems.Thm_SubscriptionPlanning_GrandOptimal_lemma_3
-- name    : SubscriptionPlanning.GrandOptimal.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:03:07.620168+00:00
-- url     : https://prove2.me/theorems/18cf2a5f-1839-474e-b439-2dba9b19399e
-- title:
--   Lemma 3, p. 13 (PDF 14), with strict λ_i SubGain(i,𝓜,r) > λ_i′ SubGain(i′,𝓜,r) (false on ties as printed) — monotone relative gains and fees
-- statement:
--   Fix rental prices $\mathbf r \ge 0$ satisfying Condition 2, and a feasible subscription planning $(p, S_1, \dots, S_n)$ (incentive constraints (3), $p(\emptyset) = 0$). If two user types $i, i'$ satisfy
--   $$\lambda_i\,\mathrm{SubGain}(i,\mathcal M,\mathbf r) > \lambda_{i'}\,\mathrm{SubGain}(i',\mathcal M,\mathbf r),$$
--   then
--   $$\frac{\mathrm{SubGain}(i,S_i,\mathbf r)}{\mathrm{SubGain}(i,\mathcal M,\mathbf r)} \ge \frac{\mathrm{SubGain}(i',S_{i'},\mathbf r)}{\mathrm{SubGain}(i',\mathcal M,\mathbf r)} \quad\text{and}\quad p(S_i) \ge p(S_{i'}).$$
--
--   Types with a higher usage-weighted gain from the grand set choose sets with a higher relative gain and pay higher fees. This monotonicity lets Mechanism 1 treat types in the order of $\lambda_i\,\mathrm{SubGain}(i,\mathcal M,\mathbf r)$.
--
--   **Formalization Note** The paper's hypothesis is the weak inequality $\ge$; it is replaced by the strict one because the lemma is false on ties: two identical types indifferent between $\mathcal M$ (priced at its full gain) and $\emptyset$ may be assigned different sets, and the lemma applied in both directions gives a contradiction. "Let $S_i$ be the optimal subscription set of user type $i$" is the incentive constraint (3). Ratios with zero denominator are $0$ in Lean. The hypothesis $\mathbf r \ge 0$ is added.
-- source:
--   Alaei, Makhdoumi, Malekian, Optimal Subscription Planning for Digital Goods, working paper (SSRN 3476296; Operations Research, doi:10.1287/opre.2023.2468), p. 13, Lemma 3 (proof pp. 28–30)

import Mathlib
import Definitions.Def_SubscriptionPlanning_GrandOptimal_Setting

namespace SubscriptionPlanning.GrandOptimal
theorem lemma_3 {n m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (M : Model n m Ω)
    (hM : M.Valid) (r : Fin m → ℝ) (hr : ∀ j, 0 ≤ r j) (hC : Condition2 M r)
    (p : Finset (Fin m) → ℝ) (S : Fin n → Finset (Fin m)) (hF : IsFeasible M r p S)
    (i i' : Fin n)
    (hlt : M.lam i' * subGain M i' Finset.univ r < M.lam i * subGain M i Finset.univ r) :
    relGain M i' (S i') r ≤ relGain M i (S i) r ∧ p (S i') ≤ p (S i) := by sorry
end SubscriptionPlanning.GrandOptimal
