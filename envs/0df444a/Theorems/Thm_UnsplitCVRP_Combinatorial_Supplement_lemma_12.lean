-- Prove2me | Theorems.Thm_UnsplitCVRP_Combinatorial_Supplement_lemma_12
-- name    : UnsplitCVRP.Combinatorial.Supplement.lemma_12
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T09:41:04.605374+00:00
-- url     : https://prove2.me/theorems/568616d8-136a-45f4-80a2-35f9c3a30da5
-- title:
--   Lemma 12, p. 9 — a big client is left uncovered with probability at most $e^{-\gamma}$
-- statement:
--   Let $\delta$ be the big/small threshold, $\mathcal J$ the set of feasible big-client tours, and let $x$ be a feasible solution of the Configuration-LP, i.e. $x_T\ge0$ for $T\in\mathcal J$ and $\sum_{T\in\mathcal J:\,v\in T}x_T\ge1$ for every big client $v$ (constraint (7)). Let $\gamma\ge0$ and sample each tour $T\in\mathcal J$ independently with probability $\min\{1,\gamma x_T\}$, giving the collection $\mathcal T$. Then for every big client $v$,
--
--   $$\Pr[v\text{ is not covered by }\mathcal T]\ \le\ e^{-\gamma}.$$
--
--   In Algorithm 2 this is applied with $\gamma=\ln 2$ and $x=x^*$, so each big client reaches the δ-tank step with probability at most $1/2$; this halves the big clients' radial contribution in the proof of Theorem 2.
--
--   **Formalization Note** The probability is the finite sum, over subcollections $S\subseteq\mathcal J$ none of whose tours contains $v$, of the product weights of the independent rounding.
--
--   Differences from the source:
--   - generalization: γ = ln 2 and x = x*, an optimal LP solution → any γ ≥ 0 and any feasible x; reason: the bound uses only x ≥ 0 and constraint (7) for v, so the source's case γ = ln 2, x = x* is an instance
--   - generalization: δ a fixed constant in (0, 1/2] → any real δ; reason: the threshold only defines which clients are big, and the bound holds for every threshold, in particular those in (0, 1/2]
--   - encoding: Pr over independently sampled tours → finite sum of product weights over subcollections of 𝒥; reason: this is the law of independent Bernoulli choices, the same distribution
-- source:
--   Friggstad, Mousavi, Rahgoshay, Salavatipour, Improved Approximations for CVRP with Unsplittable Demands, arXiv:2111.08138v1, p. 9, Lemma 12 (proof p. 10)

import Mathlib
import Definitions.Def_SupplyChainTheory_vrp
import Definitions.Def_UnsplitCVRP_Combinatorial_Setting
import Definitions.Def_UnsplitCVRP_Combinatorial_Supplement_ConfigLP

namespace UnsplitCVRP.Combinatorial.Supplement

/-- Lemma 12, p. 9: under independent rounding with probabilities `min {1, γ x_T}`,
a big client is left uncovered with probability at most `e^{-γ}`. -/
theorem lemma_12 {n : ℕ} (d : Fin (n + 1) → ℝ) (δ γ : ℝ) (hγ : 0 ≤ γ)
    (x : List (Fin (n + 1)) → ℝ) (hx : IsConfigFeasible d δ x)
    (v : Fin (n + 1)) (hv : v ∈ bigIn d δ (clients n)) :
    probNotCovered d δ γ x v ≤ Real.exp (-γ) := by sorry

end UnsplitCVRP.Combinatorial.Supplement
