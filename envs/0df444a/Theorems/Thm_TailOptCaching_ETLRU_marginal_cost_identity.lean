-- Prove2me | Theorems.Thm_TailOptCaching_ETLRU_marginal_cost_identity
-- name    : TailOptCaching.ETLRU.marginal_cost_identity
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:23:31.137067+00:00
-- url     : https://prove2.me/theorems/3b6ca5db-53af-4ff9-8be8-2a3935568c59
-- title:
--   App. B, Greedy Implementation, p. 19 — $P(L_i + Q_i - \xi \ge X_i)$ is the marginal expected cost of evicting one more token
-- statement:
--   Let the threshold $\xi$ be a natural number, let $i$ be a conversation with prompt-length law $Q_i$ on $\mathbb N$, and let $L, X \in \mathbb N$. Then
--   $$\mathbb E\big[(L + Q_i - \xi - (X - 1))^+\big] = \mathbb P(L + Q_i - \xi \ge X) + \mathbb E\big[(L + Q_i - \xi - X)^+\big].$$
--   Equivalently, $\mathbb P(L_i + Q_i - \xi \ge X_i)$ is the increase in the expected TEL of conversation $i$ caused by evicting one more of its $X_i$ cached tokens.
--
--   This is the identity behind the ranking criterion $\lambda_i\,\mathbb P(L_i + Q_i - \xi \ge X_i)$ of the greedy implementation of ET-LRU (Policy 2).
--
--   **Formalization Note.** The page writes the identity as a difference of expectations; it is stated here as a sum to avoid subtraction in $[0, \infty]$ (the two forms agree when the expectations are finite). The hypothesis $\xi \in \mathbb N$ is added: all lengths are integers, and for fractional $\xi$ the jump of $(\cdot)^+$ between $X - 1$ and $X$ is not the indicator of $\{L + Q_i - \xi \ge X\}$, so the identity fails. $X - 1$ is computed in $\mathbb R$, so $X = 0$ is allowed.
-- source:
--   Zhang, Li, Moallemi & Peng, Tail-Optimized Caching for LLM Inference, arXiv:2510.15152v1, p. 19, App. B, Greedy Implementation (unnumbered display)

import Mathlib
import Definitions.Def_TailOptCaching_ETLRU_Model

open scoped ENNReal

namespace TailOptCaching.ETLRU

theorem marginal_cost_identity (P : Params) (hξ : ∃ m : ℕ, P.ξ = m) (i L X : ℕ) :
    ∑' Q : ℕ, P.Qlaw i Q * ENNReal.ofReal ((L : ℝ) + Q - P.ξ - ((X : ℝ) - 1)) =
      tailProb P i L X + ∑' Q : ℕ, P.Qlaw i Q * ENNReal.ofReal ((L : ℝ) + Q - P.ξ - X) := by sorry

end TailOptCaching.ETLRU
