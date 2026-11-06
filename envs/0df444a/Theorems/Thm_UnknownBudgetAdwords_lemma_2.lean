-- Prove2me | Theorems.Thm_UnknownBudgetAdwords_lemma_2
-- name    : UnknownBudgetAdwords.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:22:21.421509+00:00
-- url     : https://prove2.me/theorems/e666aa41-934a-4226-aff6-bc78d540a3da
-- title:
--   Lemma 2: the candidate solution splits the reward of f-GPG exactly (corrected: Algorithm 2 step)
-- statement:
--   Let $\beta>0$ and let the candidate solution (6) be $\lambda_t=E_Y[\lambda_t(Y)]$ and $\theta_i=E_Y[\theta_i(Y)]$, with $Y$ uniform on $[0,1]^n$. Then
--
--   $$
--   \sum_{i}\theta_i+\sum_{t}\lambda_t=\text{f-GPG},
--   $$
--
--   where f-GPG is the expected reward of the algorithm, and constraint (1) holds with $\varepsilon=0$.
--
--   The reward $b_{i,t}\delta_{i,t}(Y)$ of each fractional match is split into a fraction $g(y_i)$ and a fraction $1-g(y_i)$, so that no reward is lost or double counted by the candidate solution.
--
--   Differences from the source:
--   - correction: Algorithm 2 steps by δ_{i*}(t) = min{1, B_{i*}(t−1)/b_{i*,t}}, with the argmax over I(t) → each pass matches d = min(1 − δ, R_{i*}/b_{i*,t}), with the argmax over available resources with a positive bid; reason: on budgets (0.5, 10) and one arrival with bids (1, 1) the printed step matches 1.5 of one arrival, against "until t is fully (fractionally) matched" (p.10) and the continuous description of p.16; a zero bid would also be divided by
--   - encoding: no tie rule; ties have probability 0 (pp.9, 10) → ties are broken by least index; reason: the expectation does not depend on the rule
--   - reading: (6) printed as λ_t = E_Y[λ_τ(Y)] → λ_t = E_Y[λ_t(Y)]; reason: the subscript τ is a slip: λ_τ is introduced only on p.16 and (4) defines λ_t(Y)
-- source:
--   Udwani, Adwords with Unknown Budgets and Beyond, arXiv:2110.00504v5, Lemma 2, p.15; (6), pp.13, 15

import Definitions.Def_UnknownBudgetAdwords_FGPG
open MehtaOnlineAdAllocation.MSVV
open StochasticRewardMatching.Decomposable (seedAverage)
noncomputable section

namespace UnknownBudgetAdwords

/-- Lemma 2 (Udwani, arXiv:2110.00504v5, Lemma 2, p.15): for the candidate solution (6),
`λ_t = E_Y[λ_t(Y)]`, `θ_i = E_Y[θ_i(Y)]`, the sum of all `θ_i` and `λ_t` equals the expected reward
of f-GPG, and constraint (1) holds with `ε = 0`. -/
theorem lemma_2 {N M : ℕ} (I : Instance N M) (β : ℝ) (hβ : 0 < β) : (∑ i, seedAverage (fun Y => theta I β Y i) + ∑ t, seedAverage (fun Y => lam I β Y t) = seedAverage (fValue I β)) ∧ (∑ t, seedAverage (fun Y => lam I β Y t) + ∑ i, seedAverage (fun Y => theta I β Y i) ≤ (1 + 0) * seedAverage (fValue I β)) := by sorry

end UnknownBudgetAdwords
