-- Prove2me | Theorems.Thm_SharedVehicleApprox_Pricing_Supplement_lemma_21
-- name    : SharedVehicleApprox.Pricing.Supplement.lemma_21
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T18:35:59.702006+00:00
-- url     : https://prove2.me/theorems/bf216614-027f-4f2c-9bd3-67c0bc4960e5
-- title:
--   Lemma 21, p. 25 — unit infinite-unit availabilities under supply redirection (corrected: strongly connected routing, denominator of r̃)
-- statement:
--   Let $n\ge1$, let $\varphi_{ij}\ge0$, let the reward curves be concave on $[0,1]$, and let $(\tilde q,\tilde z)$ be an optimum of Algorithm 3 with redirection costs $c_{ij}$. Put $\tilde r_{ij}=\tilde z_{ij}/\sum_k\varphi_{ki}\tilde q_{ki}$ and define the induced demand
--
--   $$\bar\varphi_{ij}=\varphi_{ij}\tilde q_{ij}\Bigl(1-\sum_k\tilde r_{jk}\Bigr)+\sum_k\varphi_{ik}\tilde q_{ik}\tilde r_{kj}.$$
--
--   Assume that $\{(a,b):a\ne b,\ \bar\varphi_{ab}>0\}$ is strongly connected. Then:
--
--   1. $\bar\varphi$ is balanced, $\sum_k\bar\varphi_{ki}=\sum_j\bar\varphi_{ij}$ at every node;
--   2. for every positive solution $r$ of the traffic equations of $\bar\varphi$, every infinite-unit availability is
--   $$A_{i,\infty}=\frac{r_i}{r_{\max}}=1.$$
--
--   The lemma replaces Lemma 10 in the proof of Theorem 22.
--
--   **Formalization Note** The infinite-unit availability is the formula of Proposition 6. Page 25 prints the denominator of $\tilde r_{ij}$ as $\sum_k\varphi_{ki}$, a misprint with which the lemma fails.
--
--   Differences from the source:
--   - correction: no connectivity hypothesis → the support graph of the induced demand φ̄ is strongly connected; reason: false without it: n = 2, m = 2, φ_ij = 1 for all pairs, I_11 = I_22 = 1, I_12 = I_21 = 0, c = 0 gives φ̄ = identity, whose traffic solution (1, 2) has availabilities (1/2, 1). Excluded: reducible induced routing
--   - correction: Algorithm 3 prints r̃_ij = z̃_ij / Σ_k φ_ki → r̃_ij = z̃_ij / Σ_k φ_ki q̃_ki (0 when the denominator is 0); reason: misprint: the text before Algorithm 3 and the third equality of the proof of Lemma 21 use this denominator. With the printed one, n = 2, φ_12 = 2, φ_21 = 1, φ_ii = 0, c = 0, R_12(q) = q(3 − 2q), R_21(q) = q gives q̃_12 = 3/4, q̃_21 = 1, z̃_21 = 1/2, infinite-unit availabilities (8/9, 1), and for m = 30 an objective below 3, less than 30/31 times the 30/31 · 13/4 earned by the repaired policy
--   - reading: Algorithm 3 lists no sign constraint on z → z_ij ≥ 0; reason: z are rates (§5.1), and a negative z would give negative probabilities
--   - reading: a cost c_ij, with no sign stated → any real c_ij; reason: the reading covers every cost matrix, so it is not a weaker one
--   - generalization: all availabilities equal one → also that the induced demand is balanced; reason: this clause is proved in the paper’s proof and only adds to the conclusion
--   - generalization: per-ride rewards of prices, with I_ij(q) := I_ij(F_ij^{-1}(1 − q)) (pp. 6–8) → arbitrary real functions I_ij of the quantile, with R_ij(q) = q · I_ij(q); no F_ij; reason: every reward induced by value distributions is such a function, so the statement specializes to the paper’s
--   - encoding: the output of Algorithm 3 → any optimal solution of its relaxation; reason: the algorithm returns an optimum; the statement holds for each one and does not need existence
--   - encoding: availability in the infinite-unit system → r_i / max_j r_j for any positive traffic solution r; reason: Proposition 6; under connectivity all positive solutions are proportional
-- source:
--   Banerjee, Freund & Lykouris, Pricing and Optimization in Shared Vehicle Systems: An Approximation Framework, arXiv:1608.06819v4, p. 25 (PDF 26), Lemma 21; proof p. 26 (PDF 27)

import Mathlib
import Definitions.Def_QueueingFundamentals_Networks_ClosedJackson
import Definitions.Def_SharedVehicleApprox_Pricing_Model
import Definitions.Def_SharedVehicleApprox_Pricing_Supplement_SupplyRedirection
import Definitions.Def_SharedVehicleApprox_Pricing_Supplement_Algorithm3

open Finset QueueingFundamentals.Networks

namespace SharedVehicleApprox.Pricing.Supplement

/-- Lemma 21, p. 25 (corrected: the induced routing is strongly connected, and the denominator
misprint in `r̃` is repaired): under `q̃` and `r̃` returned by Algorithm 3 the induced demand `φ̄` is
balanced and every availability in the infinite-unit system equals one. -/
theorem lemma_21 {n : ℕ} [NeZero n] (φ : Fin n → Fin n → ℝ) (hφ : ∀ i j, 0 ≤ φ i j)
    (I : Fin n → Fin n → ℝ → ℝ)
    (hR : ∀ i j, ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (rewardCurve I i j))
    (c qt zt : Fin n → Fin n → ℝ) (hopt : IsAlg3Optimal φ I c qt zt)
    (hconn : SupportConnected (inducedDemand φ qt (redirectProb φ qt zt)) (fun _ _ => 1)) :
    IsBalanced (inducedDemand φ qt (redirectProb φ qt zt)) (fun _ _ => 1) ∧
      ∀ r : Fin n → ℝ, (∀ i, 0 < r i) →
        IsTraffic (inducedDemand φ qt (redirectProb φ qt zt)) (fun _ _ => 1) r →
          ∀ i, availInf r i = 1 := by sorry

end SharedVehicleApprox.Pricing.Supplement
