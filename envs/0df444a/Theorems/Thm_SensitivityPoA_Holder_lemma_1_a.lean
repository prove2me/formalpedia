-- Prove2me | Theorems.Thm_SensitivityPoA_Holder_lemma_1_a
-- name    : SensitivityPoA.Holder.lemma_1_a
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T17:39:12.252819+00:00
-- url     : https://prove2.me/theorems/8221771a-58a1-4e47-a6c1-915c993022dd
-- title:
--   Lemma 1a), p. 13 — an ǫ-approximate WE flow is within ǫ of the per-pair minimum path cost
-- statement:
--   Let $\Gamma = (\tau, d)$ be a generalized nonatomic congestion game (continuous, non-decreasing, non-negative arc costs on $[0,\infty)$, non-negative demands), let $\epsilon > 0$ and let $f$ be an $\epsilon$-approximate Wardrop equilibrium flow of $\Gamma$. Then for every O/D pair $k$,
--   $$0 \le \sum_{s\in\mathcal S_k} f_s\,\tau_s(f) - d_k \min_{s'\in\mathcal S_k}\tau_{s'}(f) \le \epsilon,$$
--   and moreover
--   $$\sum_{k\in\mathcal K} d_k \min_{s'\in\mathcal S_k}\tau_{s'}(f) \le C(\Gamma, f) \le \sum_{k\in\mathcal K} d_k \min_{s'\in\mathcal S_k}\tau_{s'}(f) + \epsilon.$$
--
--   The total cost of an approximate equilibrium is thus within $\epsilon$ of what each user would pay on a cheapest path; this is the basic estimate behind Lemma 1c).
--
--   **Formalization Note** `Network.Basic` contains G1–G2 but does not impose the later Condition 1. The paper prints the first upper bound as "$< \epsilon$". Only "$\le \epsilon$" follows from (2.7), and Example 2 (p. 13: Pigou's game with $f = (1-\sqrt\epsilon, \sqrt\epsilon)$) attains equality, so the statement uses $\le$. The lemma's preamble also names a WE flow $\tilde f$, which part a) does not use; it is omitted.
-- source:
--   Wu, Möhring, A sensitivity analysis of the PoA in non-atomic congestion games, arXiv:2007.13979v3 (2021), p. 13, Lemma 1a)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_SensitivityPoA_Holder_Setting

namespace SensitivityPoA.Holder
open KellyStochasticNetworks

/-- Lemma 1a), p. 13 (printed `< ǫ` read `≤ ǫ`, attained in Example 2). -/
theorem lemma_1_a (N : Network) (hN : N.Basic) (Γ : Game N) (hΓ : Γ.IsGeneralized)
    (ε : ℝ) (hε : 0 < ε) (f : Fin N.R → ℝ) (hf : IsApproxWE Γ ε f) :
    (∀ k : Fin N.Sd,
      0 ≤ (∑ r ∈ Finset.univ.filter (fun r => N.s r = k), f r * pathCost Γ f r)
          - Γ.d k * minPathCost Γ f k ∧
      (∑ r ∈ Finset.univ.filter (fun r => N.s r = k), f r * pathCost Γ f r)
          - Γ.d k * minPathCost Γ f k ≤ ε) ∧
    (∑ k, Γ.d k * minPathCost Γ f k ≤ cost Γ f ∧
      cost Γ f ≤ (∑ k, Γ.d k * minPathCost Γ f k) + ε) := by sorry

end SensitivityPoA.Holder
