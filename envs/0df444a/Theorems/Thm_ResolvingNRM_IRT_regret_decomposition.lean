-- Prove2me | Theorems.Thm_ResolvingNRM_IRT_regret_decomposition
-- name    : ResolvingNRM.IRT.regret_decomposition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T02:21:23.184137+00:00
-- url     : https://prove2.me/theorems/3703444c-c783-42e3-a999-a79938404f6c
-- title:
--   Eq. (13), p. 29 — regret of IRT$^{K'}$ is $\sum_{u<K'} O(T^{(5/6)^u}e^{-\kappa T^{(5/6)^u/6}}) + O(T^{(5/6)^{K'}/2})$
-- statement:
--   Fix the data of the network revenue-management model: Poisson rates $\lambda_j > 0$, revenues $r_j \ge 0$ and a nonnegative bill-of-materials matrix $A$. For $K' \in \mathbb N$ let $\mathrm{IRT}^{K'}$ be the policy that re-solves the DLP at the times $t^*_u = T - T^{(5/6)^u}$, $u = 1, \dots, K'$, with thresholded acceptance probabilities in the epochs before the last re-solve and plain probabilities in the last epoch $[t^*_{K'}, T]$.
--
--   There are constants $\kappa > 0$ and $M$, depending only on $(\lambda, r, A)$, such that for every choice of optimal DLP solutions, every $T \ge 1$, every capacity $C \ge 0$ and every number of re-solves $K' \in \mathbb N$,
--   $$v^{\mathrm{HO}}(T, C) - v^{\mathrm{IRT}^{K'}}(T, C) \le M\sum_{u=0}^{K'-1} T^{(5/6)^u}\exp\big(-\kappa T^{(5/6)^u/6}\big) + M\,T^{(5/6)^{K'}/2}.$$
--
--   With $K' = K(T) = \lceil \log\log T/\log(6/5)\rceil$ this is the regret of IRT itself, and the right-hand side is then bounded independently of $T$; with $K' = 0$ it recovers SPA's $O(\sqrt T)$ regret against the hindsight optimum.
--
--   **Formalization Note** The paper states (13) for "the decision maker re-solves $K$ times" after an induction on the number of re-solves; the statement here holds for every number $K'$ of re-solves, with constants uniform in $K'$, and $K' = K(T)$ is the instance used for Theorem 1. The exponent $T^{(5/6)^u/6}$ is $T$ raised to $(5/6)^u/6$, i.e. $\tau_u^{1/6}$. $\kappa$ is existential for the reason given at Proposition 1. The standing assumptions are those of Sec. 2, p. 7. The horizon is a real $T \ge 1$.
-- source:
--   Bumpensanti, Wang, A Re-solving Heuristic with Uniformly Bounded Loss for Network Revenue Management, arXiv:1802.06192v3, Appendix B.1, eq. (13), p. 29

import Mathlib
import Definitions.Def_RLPBidPrice_Unbiased_Model
import Definitions.Def_ResolvingNRM_IRT_Model

open RLPBidPrice.Unbiased Matrix

namespace ResolvingNRM.IRT

theorem regret_decomposition {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r lam : Fin n → ℝ)
    (hlam : ∀ j, 0 < lam j) (hr : ∀ j, 0 ≤ r j) (hA : ∀ l j, 0 ≤ A l j) :
    ∃ κ : ℝ, 0 < κ ∧ ∃ M : ℝ, ∀ sel : (Fin m → ℝ) → (Fin n → ℝ), IsDLPSelector A r lam sel →
      ∀ T : ℝ, 1 ≤ T → ∀ C : Fin m → ℝ, 0 ≤ C → ∀ K' : ℕ,
        hindsightValue A r lam T C - irtValue A r lam sel K' T C ≤
          M * (∑ u ∈ Finset.range K',
              T ^ ((5 / 6 : ℝ) ^ u) * Real.exp (-κ * T ^ ((5 / 6 : ℝ) ^ u / 6))) +
            M * T ^ ((5 / 6 : ℝ) ^ K' / 2) := by sorry

end ResolvingNRM.IRT
