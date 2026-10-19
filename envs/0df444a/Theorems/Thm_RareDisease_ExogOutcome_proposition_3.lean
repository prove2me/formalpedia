-- Prove2me | Theorems.Thm_RareDisease_ExogOutcome_proposition_3
-- name    : RareDisease.ExogOutcome.proposition_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T09:43:08.180431+00:00
-- url     : https://prove2.me/theorems/ca7a5495-ce76-4f9c-a446-2db48e55a5d2
-- title:
--   Proposition 3(1),(3), p. 15 — the budget binds; patient-only subsidy if p ≥ 2/(5 − αmax), manufacturer-only if p ≤ 2(1 − αmax)/5
-- statement:
--   Consider Setting (2B): the consortium fixes the unit price $p\in(0,1)$, the manufacturer is paid only when the drug is efficacious and best-responds to a subsidy policy $(\alpha,\beta)\in[0,1)^2$ by choosing its target efficacy $e>0$, and the government chooses the policy to maximize patient welfare subject to spending at most the budget $B>0$; the R&D cost scale is $k>0$. Let $\alpha_{\max}$ be the largest $\alpha\in[0,1)$ such that the policy $(\alpha,0)$ is affordable at the manufacturer's best response. Then:
--
--   1. **(binding budget)** at every optimal policy the spending at the manufacturer's best response equals $B$;
--   2. **(Proposition 3, part 1)** if $p\ge \dfrac{2}{5-\alpha_{\max}}$ and $B<\dfrac{p^2}{2k}$, it is optimal to subsidize patients only: there is $\beta_1$ such that $(0,\beta_1)$ is an optimal policy, and every optimal policy equals $(0,\beta_1)$;
--   3. **(Proposition 3, part 3)** if $p\le \dfrac{2(1-\alpha_{\max})}{5}$, it is optimal to subsidize the manufacturer only: $(\alpha_{\max},0)$ is an optimal policy, every optimal policy equals it, and
--   $$\alpha_{\max}=\frac{8Bk+p^4-2p^3+p^2-(p-p^2)\sqrt{16Bk+p^4-2p^3+p^2}}{8Bk}.$$
--
--   The result says that under a consortium price with "No Cure No Pay" payment the government's whole budget goes to one side of the market when the price is high (patients) or low (the manufacturer).
--
--   **Formalization Note** Part 2 of the printed proposition (both subsidies when $2(1-\alpha_{\max})/5<p<2/(5-\alpha_{\max})$) is not posed: it is false as printed (for $B=0.05$, $k=0.3$, $p=0.2$ the price lies in that range but the unique optimum is manufacturer-only). The printed closed form for $\beta$ in part 1 is not posed either, because it does not satisfy the binding constraint; $\beta_1$ is characterized by the binding clause instead. Part 1 adds the hypothesis $B<p^2/(2k)$: at $\alpha=0$ the spending tends to $p^2/(2k)$ as $\beta\uparrow1$, so for larger budgets no patient-only policy exhausts the budget. The hypotheses $k>0$, $B>0$ and $0<p<1$ are the paper's standing assumptions made explicit. "Optimal" quantifies over every policy and every best response; efficacies are not bounded by $1$, as in the paper.
-- source:
--   Olsder, Martagan, Tang, Improving Access to Rare Disease Treatments: Optimal Subsidies, Pricing, and Payment, SSRN working paper 3481150 (version of 2019-11-13), p. 15, Proposition 3, parts 1 and 3 (and its first sentence)

import Mathlib
import Definitions.Def_RareDisease_ExogOutcome_Setting

namespace RareDisease.ExogOutcome

/-- Proposition 3, p. 15, parts 1 and 3 (with the binding budget constraint), Setting (2B).
`a` is `α_max`. Part 1 adds the disclosed hypothesis `B < p² / (2k)`; part 2 and the printed
closed form of part 1 are not posed (both are false as printed). -/
theorem proposition_3 (k B p : ℝ) (hk : 0 < k) (hB : 0 < B) (hp0 : 0 < p) (hp1 : p < 1)
    (a : ℝ) (ha : IsAlphaMax k p B a) :
    (∀ α β : ℝ, IsOptimal k p B α β → ∀ e ∈ BR k p α β, spend k p α β e = B) ∧
    (2 / (5 - a) ≤ p → B < p ^ 2 / (2 * k) →
      ∃ β₁ : ℝ, IsOptimal k p B 0 β₁ ∧
        ∀ α β : ℝ, IsOptimal k p B α β → α = 0 ∧ β = β₁) ∧
    (p ≤ 2 * (1 - a) / 5 →
      IsOptimal k p B a 0 ∧
        (∀ α β : ℝ, IsOptimal k p B α β → α = a ∧ β = 0) ∧
        a = (8 * B * k + p ^ 4 - 2 * p ^ 3 + p ^ 2
              - (p - p ^ 2) * Real.sqrt (16 * B * k + p ^ 4 - 2 * p ^ 3 + p ^ 2)) / (8 * B * k)) := by sorry

end RareDisease.ExogOutcome
