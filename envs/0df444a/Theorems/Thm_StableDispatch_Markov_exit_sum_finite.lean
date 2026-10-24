-- Prove2me | Theorems.Thm_StableDispatch_Markov_exit_sum_finite
-- name    : StableDispatch.Markov.exit_sum_finite
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:42:10.33272+00:00
-- url     : https://prove2.me/theorems/e040d587-fbd4-4b9c-a919-1e8268346eb4
-- title:
--   Appendix A, p. 15, after (A.1) — the Ξ-weighted transition rates out of every state have a finite sum
-- statement:
--   Fix $n\ge1$, $\lambda\in(0,1)$, $\alpha_n>0$ and $\mu\in\Sigma_n$, and let $r_{x\to y}$ be the transition rates of the chain $(Q(\cdot),I(\cdot))$ of the single-ID policy. With the Lyapunov function $\Xi=\Xi_1+\Xi_2$ of (A.1), for every state $(q,i)\in\mathbb Z_+^n\times\{1,\dots,n\}$,
--   $$\sum_{(q',i')\ne(q,i)}\Xi(q',i')\,r_{(q,i)\to(q',i')}<\infty .$$
--
--   This finiteness is one of the conditions of the Foster–Lyapunov criterion invoked at the end of the proof of Theorem 2.1.
--
--   Differences from the source:
--   - encoding: the sum of nonnegative terms is < ∞ → the family y ↦ Ξ(y)·r_{x→y} (0 at y = x) is `Summable` in ℝ; reason: the terms are nonnegative, so summability is exactly finiteness of the sum
--   - encoding: n arbitrary → `[NeZero n]`; reason: μ_max in Ξ1 is undefined for n = 0 (no servers)
--   - encoding: servers {1, …, n} → `Fin n` (0-based); reason: Lean convention, same instances
-- source:
--   Gamarnik, Tsitsiklis, Zubeldia, Stability, Memory, and Messaging Trade-Offs in Heterogeneous Service Systems, arXiv:2007.07219v1, p. 15, Appendix A, after (A.1)

import Mathlib
import Definitions.Def_MatrixAnalytic_Tree_Process
import Definitions.Def_StableDispatch_Markov_Setting

namespace StableDispatch.Markov

theorem exit_sum_finite (n : ℕ) [NeZero n] (lam α : ℝ) (μ : Fin n → ℝ) (hlam0 : 0 < lam)
    (hlam1 : lam < 1) (hα : 0 < α) (hμ : μ ∈ Sigma n) :
    ∀ x : State n,
      Summable (fun y : State n => if y = x then 0 else Xi μ α y * gen n lam α μ x y) := by sorry

end StableDispatch.Markov
