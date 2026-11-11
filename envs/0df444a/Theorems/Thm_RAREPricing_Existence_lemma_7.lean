-- Prove2me | Theorems.Thm_RAREPricing_Existence_lemma_7
-- name    : RAREPricing.Existence.lemma_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:25:55.569954+00:00
-- url     : https://prove2.me/theorems/cd4ea81b-fce8-4e80-8128-79674d6c7d84
-- title:
--   Lemma 7 — a deviation above L_j has a response in ∏[p_k, B] under which j loses and every responder gains
-- statement:
--   Fix a market and a setting with constants $\nu,\beta,\kappa$, and a continuous allocation rule $A$. Let $(\rho_k,\sigma_k,L_k)_{k\in[m]}$ be any family of parameters as in Section 5.3: $(\rho_k,\sigma_k)$ satisfies the conclusion of Lemma 5 and $L_k$ the conclusion of Lemma 6, for every $k$. Let $p\in\beta\Delta_m$ and $j$ a seller with $p_j\ge\beta\rho_j/B$. For every deviation $q_j>L_j$ there is a response $q_{-j}\in\prod_{k\ne j}[p_k,B]$ such that, with $q=(q_j,q_{-j})$,
--   $$R^A_j(q)<\nu p_j\qquad\text{and}\qquad R^A_k(q)\ge\nu p_k\ \ \forall k\ne j .$$
--
--   Differences from the source:
--   - generalization: $(L_j)$ "as in Lemma 6" → every family $(\rho,\sigma,L)$ satisfying the conclusions of Lemmas 5 and 6; reason: the proof uses only those conclusions, and the paper's parameters are one such family.
--   - encoding: response $q_{-j}$ and $q=(q_j,q_{-j})$ → `r` with $p_k\le r_k\le B$ for $k\ne j$ and $q=$ `Function.update r j qj`; reason: the $j$-th entry of `r` is overwritten.
-- source:
--   Chaudhury, Garg, Huang, Sharma, RARE: Response-Aware Rational Equilibrium in Budget-Constrained Pricing Games, STOC 2027 submission (manuscript sha256 e9bb863f…), p. 21 (PDF 23), Lemma 7

import Mathlib
import Definitions.Def_RAREPricing_Existence_Model

namespace RAREPricing.Existence

theorem lemma_7 {n m : ℕ} (M : Market n m) (s : Setting)
    (A : (Fin m → ℝ) → (Fin n → Fin m → ℝ)) (hA : IsContinuousAllocationRule M s A)
    (ρ σ L : Fin m → ℝ) (hsec : ∀ k, IsSecurityPair M s k (ρ k) (σ k))
    (hover : ∀ k, IsOverpricingBound M s k (ρ k) (σ k) (L k))
    (p : Fin m → ℝ) (hp : p ∈ scaledSimplex m (beta M s))
    (j : Fin m) (hpj : beta M s * ρ j / M.totalBudget ≤ p j)
    (qj : ℝ) (hqj : L j < qj) :
    ∃ r : Fin m → ℝ, (∀ k, k ≠ j → p k ≤ r k ∧ r k ≤ M.totalBudget) ∧
      revA A j (Function.update r j qj) < nu M s * p j ∧
      ∀ k, k ≠ j → nu M s * p k ≤ revA A k (Function.update r j qj) := by sorry

end RAREPricing.Existence
