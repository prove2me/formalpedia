-- Prove2me | Theorems.Thm_StaticReusable_Guarantee_lemma_1
-- name    : StaticReusable.Guarantee.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:24:57.313157+00:00
-- url     : https://prove2.me/theorems/075ac05b-e705-454e-bcc8-d5277017a510
-- title:
--   Lemma 1, p. 11 — optimal arrival rates increase with the number of free units and stay below the myopic rate
-- statement:
--   Let $(C, \mu, \Lambda, c, p, \alpha_1, \alpha_2, \alpha_3)$ satisfy the standing assumptions of the instance class $\Omega$, and assume moreover $\alpha_1 > 0$ and that the profit rate $\lambda \mapsto \lambda(p(\lambda) - c)$ is **strictly** concave on $[0,\Lambda]$. Let $\bar\lambda \in [0,\Lambda]$ maximize the myopic objective $\lambda(\alpha_1(p(\lambda) - c) + \alpha_2)$ over $[0,\Lambda]$, and let $\lambda^* = (\lambda^*_1, \dots, \lambda^*_C)$ be a stationary policy that maximizes $\alpha_1 \mathcal P^\pi + \alpha_2 \mathcal{MS}^\pi + \alpha_3 \mathcal{SL}^\pi$ over all stationary policies with rates in $[0,\Lambda]$. Then
--   $$\bar\lambda \ge \lambda^*_C, \qquad \text{and} \qquad \lambda^*_i \le \lambda^*_j \quad \text{whenever } 1 \le i \le j \le C \text{ and } \mathbb P_i(\lambda^*) > 0.$$
--   On the states that the optimal policy reaches, this is the chain $\bar\lambda \ge \lambda^*_C \ge \dots \ge \lambda^*_1$ of (8): with more free units the provider charges less, and never less than the myopic price.
--
--   This structural property is what the paper's proof of Theorem 1 uses to work with $z$-variables built from monotone rates (property (EC.2), p. ec5, in the proof of Lemma 2).
--
--   **Formalization Note** The paper speaks of "the optimal arrival rate", presuming uniqueness. As printed for every optimal policy the monotonicity is false in two ways: a state $i$ with $\mathbb P_i(\lambda^*) = 0$ (below a zero rate) is never visited, so its rate is arbitrary in a maximizer; and with $\alpha_1 = 0$ the per-state problem is linear and can have many maximizers. The statement therefore adds $\alpha_1 > 0$, strict concavity of the profit rate (which together make the per-state maximizers unique), and the guard $\mathbb P_i(\lambda^*) > 0$. State $C$ always has positive probability, so $\bar\lambda \ge \lambda^*_C$ needs no guard. Optimality is `IsMaxOn` over the stationary policies with rates in $[0,\Lambda]$; existence of an optimal policy is not asserted.
-- source:
--   Besbes, Elmachtoub and Sun, Static Pricing: Universal Guarantees for Reusable Resources, arXiv:1905.00731v3, p. 11, Lemma 1, (8); proof EC.2, pp. ec3–ec5 (PDF 24–26)

import Mathlib
import Definitions.Def_StaticReusable_Guarantee_Setting

open Finset

namespace StaticReusable.Guarantee

theorem lemma_1 {C : ℕ} {μ Λ c α₁ α₂ α₃ : ℝ} {p : ℝ → ℝ}
    (hS : Standing C μ Λ c p α₁ α₂ α₃) (hα₁ : 0 < α₁)
    (hstrict : StrictConcaveOn ℝ (Set.Icc 0 Λ) (fun l => l * (p l - c)))
    (lbar : ℝ) (hlbar : lbar ∈ Set.Icc 0 Λ)
    (hmyopic : IsMaxOn (myopic p c α₁ α₂) (Set.Icc 0 Λ) lbar)
    (lamStar : ℕ → ℝ) (hpol : lamStar ∈ Policies C Λ)
    (hopt : IsMaxOn (value C μ p c α₁ α₂ α₃) (Policies C Λ) lamStar) :
    lamStar C ≤ lbar ∧
      ∀ i j : ℕ, 1 ≤ i → i ≤ j → j ≤ C → 0 < prob C μ lamStar i → lamStar i ≤ lamStar j := by sorry
end StaticReusable.Guarantee
