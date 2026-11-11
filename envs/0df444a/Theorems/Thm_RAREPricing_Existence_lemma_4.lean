-- Prove2me | Theorems.Thm_RAREPricing_Existence_lemma_4
-- name    : RAREPricing.Existence.lemma_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:26:00.135905+00:00
-- url     : https://prove2.me/theorems/132314dc-9edd-4b6c-9b3f-3b20d5956de1
-- title:
--   Lemma 4 — prices in βΔ_m where every bounded deviation has a bounded market-share-preserving response
-- statement:
--   Fix a market and a setting with constants $\nu,\beta$, let $A$ be a continuous allocation rule, and let $L_j\ge\beta$ for each seller $j$. Then there is $p\in\beta\Delta_m$ such that for every seller $j$ and every deviation $q_j\in[p_j,L_j]$ there is a response $q_{-j}\in\prod_{k\ne j}[p_k,L_k]$ with, for $q=(q_j,q_{-j})$,
--   $$\frac{R^A_k(q)}{R_{\mathrm{all}}(q)}=\frac{p_k}{\beta}\qquad\text{for every seller }k\in[m].$$
--
--   This is the outer KKM step (applied to the sets $C_j$ of Eq. (2)); Theorem 1 handles deviations above $L_j$ separately.
--
--   **Formalization Note.** $q=(q_j,q_{-j})$ is `Function.update r j qj`; the bounds on `r` are imposed for $k\ne j$ only. Division is Lean's ($a/0=0$); no instance is affected, since $\sum_kp_k/\beta=1$ forces $R_{\mathrm{all}}(q)\ne0$ whenever the equalities hold.
--
--   Differences from the source:
--   - encoding: response $q_{-j}\in\prod_{k\ne j}[p_k,L_k]$ and $q=(q_j,q_{-j})$ → `r : Fin m → ℝ` with $p_k\le r_k\le L_k$ for $k\ne j$, $q=$ `Function.update r j qj`; reason: the $j$-th entry of `r` is overwritten, so the same responses.
-- source:
--   Chaudhury, Garg, Huang, Sharma, RARE: Response-Aware Rational Equilibrium in Budget-Constrained Pricing Games, STOC 2027 submission (manuscript sha256 e9bb863f…), p. 19 (PDF 21), Lemma 4

import Mathlib
import Definitions.Def_RAREPricing_Existence_Model

namespace RAREPricing.Existence

theorem lemma_4 {n m : ℕ} (M : Market n m) (s : Setting)
    (A : (Fin m → ℝ) → (Fin n → Fin m → ℝ)) (hA : IsContinuousAllocationRule M s A)
    (L : Fin m → ℝ) (hL : ∀ j, beta M s ≤ L j) :
    ∃ p ∈ scaledSimplex m (beta M s), ∀ j : Fin m, ∀ qj : ℝ, p j ≤ qj → qj ≤ L j →
      ∃ r : Fin m → ℝ, (∀ k, k ≠ j → p k ≤ r k ∧ r k ≤ L k) ∧
        ∀ k, revA A k (Function.update r j qj) / totalRevA A (Function.update r j qj) =
          p k / beta M s := by sorry

end RAREPricing.Existence
