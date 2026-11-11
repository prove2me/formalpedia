-- Prove2me | Theorems.Thm_RAREPricing_Existence_theorem_1
-- name    : RAREPricing.Existence.theorem_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:26:01.161442+00:00
-- url     : https://prove2.me/theorems/a4b5c4c9-6a82-4206-9748-965db2b51b2f
-- title:
--   Theorem 1 — a κ-RARE in the truncated simplex with responses in ∏[p_k, L_k]
-- statement:
--   Fix a market $I$, a setting with constants $\nu,\beta,\kappa=B/(\nu\beta)$, and a continuous allocation rule $A$. Let $(\rho_k,\sigma_k,L_k)_{k\in[m]}$ be any family of parameters as in Section 5.3: for each $k$, $(\rho_k,\sigma_k)$ satisfies the conclusion of Lemma 5 and $L_k$ the conclusion of Lemma 6. Then there is a price vector $p$ in the truncated simplex $\{y\in\beta\Delta_m: y_j\ge\beta\rho_j/B\ \forall j\}$ such that for every seller $j$ and every deviation $q_j\ge0$ there is a response $q_{-j}\in\prod_{k\ne j}[p_k,L_k]$ with, for $q=(q_j,q_{-j})$,
--   1. $R^A_j(q)\le\kappa\cdot\nu p_j=\kappa\cdot R^A_j(p)$;
--   2. $R^A_k(q)\ge\nu p_k\ge R^A_k((q_j,p_{-j}))$ for every $k\ne j$.
--
--   In particular $p$ is a $\kappa$-RARE (Corollary 1). The concavity of utilities is not assumed.
--
--   Differences from the source:
--   - generalization: parameters $(\rho_j),(L_j)$ "as in Section 5.3" → every family $(\rho,\sigma,L)$ satisfying the conclusions of Lemmas 5 and 6 for every seller; reason: the proof uses only those conclusions, and the paper's parameters are one such family.
--   - encoding: response $q_{-j}$ and $q=(q_j,q_{-j})$ → `r` with $p_k\le r_k\le L_k$ for $k\ne j$ and $q=$ `Function.update r j qj`; reason: the $j$-th entry of `r` is overwritten.
-- source:
--   Chaudhury, Garg, Huang, Sharma, RARE: Response-Aware Rational Equilibrium in Budget-Constrained Pricing Games, STOC 2027 submission (manuscript sha256 e9bb863f…), pp. 21–22 (PDF 23–24), Theorem 1

import Mathlib
import Definitions.Def_RAREPricing_Existence_Model

namespace RAREPricing.Existence

theorem theorem_1 {n m : ℕ} (M : Market n m) (s : Setting)
    (A : (Fin m → ℝ) → (Fin n → Fin m → ℝ)) (hA : IsContinuousAllocationRule M s A)
    (ρ σ L : Fin m → ℝ) (hsec : ∀ k, IsSecurityPair M s k (ρ k) (σ k))
    (hover : ∀ k, IsOverpricingBound M s k (ρ k) (σ k) (L k)) :
    ∃ p ∈ scaledSimplex m (beta M s), (∀ j, beta M s * ρ j / M.totalBudget ≤ p j) ∧
      ∀ j : Fin m, ∀ qj : ℝ, 0 ≤ qj →
        ∃ r : Fin m → ℝ, (∀ k, k ≠ j → p k ≤ r k ∧ r k ≤ L k) ∧
          (revA A j (Function.update r j qj) ≤ kappa M s * (nu M s * p j) ∧
            kappa M s * (nu M s * p j) = kappa M s * revA A j p) ∧
          ∀ k, k ≠ j → nu M s * p k ≤ revA A k (Function.update r j qj) ∧
            revA A k (Function.update p j qj) ≤ nu M s * p k := by sorry

end RAREPricing.Existence
