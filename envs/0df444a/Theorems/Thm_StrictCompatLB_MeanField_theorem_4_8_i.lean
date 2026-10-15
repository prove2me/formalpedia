-- Prove2me | Theorems.Thm_StrictCompatLB_MeanField_theorem_4_8_i
-- name    : StrictCompatLB.MeanField.theorem_4_8_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:51:50.396011+00:00
-- url     : https://prove2.me/theorems/af204f61-7387-43e8-bfbc-076260d9e74d
-- title:
--   Theorem 4.8(i) — for all large N, JSQ(d) on subcritical graphs has a unique stationary distribution
-- statement:
--   Let $0<\lambda<1$, $d\ge1$, and let $\{G_N\}_{N\ge1}$ be a sequence of connected graphs satisfying the subcriticality condition. There exists $N_0\ge1$ such that for each $N\ge N_0$ the Markov process $\Phi(G_N,\cdot)$ under the JSQ(d) policy is positive Harris recurrent, and thus has a unique steady state.
--
--   Stability for all large $N$ is what allows one to speak of the steady state $\Phi(G_N,\infty)$ and to interchange the limits $t\to\infty$ and $N\to\infty$.
--
--   **Formalization Note** The conclusion is rendered as existence and uniqueness of a stationary distribution of the uniformised chain (whose stationary distributions are those of the continuous-time process). For this countable chain, in which the empty state is reachable from every state, this is equivalent to positive recurrence of the class containing the empty state; it is the part of positive Harris recurrence that the rest of the paper uses.
-- source:
--   Rutten & Mukherjee, Load Balancing Under Strict Compatibility Constraints, arXiv:2008.07562v2, p. 20, Theorem 4.8(i)

import Mathlib
import Definitions.Def_StrictCompatLB_MeanField_Model

open Filter Topology MeasureTheory
open scoped ENNReal

namespace StrictCompatLB.MeanField

/-- Theorem 4.8(i) (p. 20). For a sequence of connected graphs satisfying the subcriticality
condition, there is `N₀ ≥ 1` such that for each `N ≥ N₀` the JSQ(d) process on `G_N` (`d ≥ 1`)
has a unique stationary distribution (rendered on the uniformised chain, whose stationary
distributions are those of the process). -/
theorem theorem_4_8_i (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam < 1) (d : ℕ) (hd : 1 ≤ d)
    (M : ℕ → ℕ) (hM : ∀ N, 0 < M N) (G : (N : ℕ) → Finset (Fin N × Fin (M N)))
    (hconn : IsConnectedSeq M G) (hsub : IsSubcritical d M G) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N ≥ N₀, ∃! π : (Fin N → ℕ) → ℝ,
      IsStationary (jsqdKernel lam d M G N) π := by sorry

end StrictCompatLB.MeanField
