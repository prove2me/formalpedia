-- Prove2me | Theorems.Thm_UnknownBudgetAdwords_lemma_1
-- name    : UnknownBudgetAdwords.lemma_1
-- status  : Proved
-- author  : @iris
-- created : 2026-11-05T20:20:11.466558+00:00
-- url     : https://prove2.me/theorems/7ead524a-8f8f-4c59-b196-b03905fbd1a7
-- title:
--   Lemma 1: a solution of (1)–(3) certifies the ratio $\alpha/(1+\varepsilon)$
-- statement:
--   Let $\tau$ be an allocation and write $\mathrm{OPT}_i$ for its reward on resource $i$, $\mathrm{OPT}_i$ also standing for the set of arrivals it matches to $i$, and $\mathrm{OPT}=\sum_i\mathrm{OPT}_i$. Let $\mathrm{ALG},\alpha,\varepsilon$ be reals with $1+\varepsilon>0$, and suppose that the numbers $\lambda_t,\theta_i$ satisfy
--
--   $$
--   \sum_{t}\lambda_t+\sum_i\theta_i\le(1+\varepsilon)\,\mathrm{ALG},\qquad
--   \theta_i+\sum_{t\in\mathrm{OPT}_i}\lambda_t\ge\alpha\,\mathrm{OPT}_i\ \ \forall i,\qquad
--   \lambda_t\ge0,\ \theta_i\ge0.
--   $$
--
--   Then
--
--   $$
--   \mathrm{ALG}\ge\frac{\alpha}{1+\varepsilon}\,\mathrm{OPT}.
--   $$
--
--   This is the LP-free framework in which the paper proves Theorem 2: any feasible solution of the system is a certificate of competitiveness.
--
--   Differences from the source:
--   - encoding: "c competitive" against the optimal offline allocation → the inequality c · revenue I τ ≤ expected reward for every allocation τ; reason: there are finitely many allocations, so a bound for every τ is exactly a bound for the optimal one, and no division by OPT is needed; revenue is the capped reward of p.7, with r_i = 1 w.l.o.g. (p.7)
--   - generalization: OPT_i, the optimal offline allocation → τ any allocation; reason: the proof uses only feasibility of OPT, so the statement specializes to τ optimal
--   - encoding: (1 + ε) with ε unspecified → the hypothesis 0 < 1 + ε; reason: the ratio α/(1 + ε) needs a positive denominator
-- source:
--   Udwani, Adwords with Unknown Budgets and Beyond, arXiv:2110.00504v5, Lemma 1, p.12; (1)–(3), p.12

import Definitions.Def_MehtaOnlineAdAllocation_MSVV_Spend
open MehtaOnlineAdAllocation.MSVV
noncomputable section

namespace UnknownBudgetAdwords

/-- Lemma 1 (Udwani, arXiv:2110.00504v5, Lemma 1, p.12): a solution `λ, θ` of the system (1)–(3),
with `OPT_i` the reward of the allocation `τ` on `i`, gives
`ALG ≥ α / (1 + ε) · OPT`.

**Formalization Note** Competitive means the inequality against every allocation `τ`, the optimal
one included. `0 < 1 + ε` keeps the ratio meaningful. -/
theorem lemma_1 {N M : ℕ} (I : Instance N M) (τ : Allocation N M) (lamv : Fin M → ℝ) (thetav : Fin N → ℝ) (ALG α ε : ℝ) (hε : 0 < 1 + ε) (h1 : ∑ t, lamv t + ∑ i, thetav i ≤ (1 + ε) * ALG) (h2 : ∀ i, α * spend I τ i M ≤ thetav i + ∑ t ∈ Finset.univ.filter (fun t => τ t = some i), lamv t) (h3 : (∀ t, 0 ≤ lamv t) ∧ ∀ i, 0 ≤ thetav i) : α / (1 + ε) * revenue I τ ≤ ALG := by sorry

end UnknownBudgetAdwords
