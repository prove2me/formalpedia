-- Prove2me | Theorems.Thm_PrivacyParadox_Alloc_lemma_3
-- name    : PrivacyParadox.Alloc.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:37:28.563111+00:00
-- url     : https://prove2.me/theorems/acc792e7-53bc-4310-84dd-91c025906815
-- title:
--   Lemma 3, p. 24 — given p > 0, the analyst's best response is A*_k = min{1, √(γp_k/(s θ̄*² λ*φ_k))} with the budget binding
-- statement:
--   In the discrete program (39), fix an admissible adversary choice $p$.
--
--   1. If $p_k=0$ for all $k$, every feasible allocation is a best response of the minimizing player: $U(A,p)\le U(A',p)$ for all feasible $A,A'$.
--   2. If $0<p_k\le1$ for all $k$, and $\lambda^*>0$ is such that the allocation
--   $$A^*_k=\min\Big\{1,\sqrt{\frac{\gamma p_k}{s(\bar\theta^*)^2\lambda^*\phi_k}}\Big\}$$
--   exhausts the budget, $\sum_k\pi_k\phi_kA^*_k+l=B/s$ (46), then $A^*$ is feasible and minimizes $U(\cdot,p)$ over all feasible allocations.
--
--   This is the minimizing player's half of the saddle-point analysis of (39).
--
--   **Formalization Note** Feasibility requires $A_k>0$ (Lean's $p/0=0$); the paper's $A_{ij}\in[0,1]$ in the first bullet is read with this convention. The multiplier $\lambda^*$ is a hypothesis, as "where $\lambda^*$ is such that (46)" on the page.
-- source:
--   Liao, Su, Ziani, Wierman, Huang, arXiv:2105.14262v1, p. 24, Lemma 3, (45)–(46) (proof pp. 24–25, (47)–(50))

import Mathlib
import Definitions.Def_PrivacyParadox_Alloc_Model

namespace PrivacyParadox.Alloc

theorem lemma_3 (P : Prog) (hP : P.Standing) (p : ℕ → ℝ) :
    ((∀ k ∈ Finset.Icc 1 P.K, p k = 0) →
        ∀ A : ℕ → ℝ, P.FeasA A → ∀ A' : ℕ → ℝ, P.FeasA A' → P.U A p ≤ P.U A' p) ∧
      ((∀ k ∈ Finset.Icc 1 P.K, 0 < p k ∧ p k ≤ 1) → ∀ lam : ℝ, 0 < lam →
        ∑ k ∈ Finset.Icc 1 P.K, P.pr k * P.phi k * P.clipA p lam k + P.l = P.B / P.s →
        P.FeasA (P.clipA p lam) ∧
          ∀ A : ℕ → ℝ, P.FeasA A → P.U (P.clipA p lam) p ≤ P.U A p) := by sorry

end PrivacyParadox.Alloc
