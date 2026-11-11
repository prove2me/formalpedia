-- Prove2me | Theorems.Thm_RAREPricing_Existence_corollary_1
-- name    : RAREPricing.Existence.corollary_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:26:16.84959+00:00
-- url     : https://prove2.me/theorems/d9e8d047-8c4d-4c7e-a3fb-66f0c378a831
-- title:
--   Corollary 1 — under a continuous allocation rule a κ-RARE with total revenue B/κ exists (κ = 1 rivalrous, κ = b_avg/b_min non-rivalrous)
-- statement:
--   Let $I$ be any market: $n\ge1$ buyers, $m\ge2$ goods, budgets $b_i>0$, utilities $u_i$ on $[0,1]^m$ that are continuous, strictly monotone and vanish at $0$; $B=\sum_ib_i$, $b_{\mathrm{avg}}=B/n$, $b_{\min}=\min_ib_i$.
--   1. (rivalrous) For every continuous allocation rule $A$ with $A(p)\in\mathrm{DemR}(p)$ for all $p\ge0$, there is $p\in\mathbb R^m_{\ge0}$ that is a $1$-RARE (Definition 2 with $\delta=0$, $\kappa=1$) with $R_{\mathrm{all}}(p)=B/1$.
--   2. (non-rivalrous) For every continuous allocation rule $A$ with $A(p)\in\mathrm{DemNR}(p)$ for all $p\ge0$, there is $p\in\mathbb R^m_{\ge0}$ that is a $\kappa$-RARE with $\kappa=b_{\mathrm{avg}}/b_{\min}$ and
--   $$R_{\mathrm{all}}(p)=\sum_{j=1}^m R^A_j(p)=\frac{B}{\kappa}.$$
--
--   Being a $\kappa$-RARE means: for every seller $j$ and every deviation $q_j\ge0$ there is a response $q_{-j}\ge0$ with $R^A_j(q)\le\kappa R^A_j(p)$ and $R^A_k(q)\ge R^A_k((q_j,p_{-j}))$ for every $k\ne j$, where $q=(q_j,q_{-j})$. Nash equilibria need not exist in these pricing games; this is the paper's existence result for the response-aware notion. No concavity of utilities is assumed; the statement is vacuous for a market that admits no continuous allocation rule.
--
--   Differences from the source:
--   - encoding: one statement with "$\kappa=1$ in the rivalrous setting and $\kappa=b_{\mathrm{avg}}/b_{\min}$ in the non-rivalrous setting" → a conjunction of the two settings, with $\kappa$ written out in each; reason: the same two claims.
-- source:
--   Chaudhury, Garg, Huang, Sharma, RARE: Response-Aware Rational Equilibrium in Budget-Constrained Pricing Games, STOC 2027 submission (manuscript sha256 e9bb863f…), p. 22 (PDF 24), Corollary 1

import Mathlib
import Definitions.Def_RAREPricing_Existence_Model

namespace RAREPricing.Existence

theorem corollary_1 {n m : ℕ} (M : Market n m) :
    (∀ A : (Fin m → ℝ) → (Fin n → Fin m → ℝ), IsContinuousAllocationRule M .rivalrous A →
      ∃ p : Fin m → ℝ, IsRARE A 0 1 p ∧ totalRevA A p = M.totalBudget / 1) ∧
    (∀ A : (Fin m → ℝ) → (Fin n → Fin m → ℝ), IsContinuousAllocationRule M .nonrivalrous A →
      ∃ p : Fin m → ℝ, IsRARE A 0 (M.bavg / M.bmin) p ∧
        totalRevA A p = M.totalBudget / (M.bavg / M.bmin)) := by sorry

end RAREPricing.Existence
