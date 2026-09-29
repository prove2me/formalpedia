-- Prove2me | Theorems.Thm_SatiaLave_MaxMin_eq5_presentValue_unique
-- name    : SatiaLave.MaxMin.eq5_presentValue_unique
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T00:37:41.676627+00:00
-- url     : https://prove2.me/theorems/4fdd3542-3530-49fc-b1c7-3f7af7debd07
-- title:
--   Eq. (5) — the present-value equations have a unique solution
-- statement:
--   Let $A$ be a pure stationary policy and $P\in S$ an admissible choice of nature, with transition probabilities $p^{A_i}_{ij}$, rewards $r^{A_i}_{ij}$ and discount factor $0\le\beta<1$. The present-value equations (5),
--   $$v_i=\sum_j p^{A_i}_{ij}\big(r^{A_i}_{ij}+\beta v_j\big),\qquad i=1,\dots,N,$$
--   have exactly one solution $v$, namely the present-value vector $v^A=[I-\beta P^A]^{-1}\big(\sum_j p^{A_i}_{ij}r^{A_i}_{ij}\big)_i$.
--
--   This justifies Phase 1(a) of the algorithm ("use $p_i^A$ to solve (5) for $v_i$") and shows that the matrix-inverse definition of the present value is the paper's object.
-- source:
--   Satia and Lave, Markovian Decision Processes with Uncertain Transition Probabilities, Operations Research 21(3), 1973, p. 730, Eq. (5)

import Mathlib
import Definitions.Def_SatiaLave_MaxMin_Model

namespace SatiaLave.MaxMin

/-- Eq. (5), p. 730: for every policy `A` and every admissible choice `P` of nature, the
present-value equations `v_i = Σ_j p^A_ij (r^A_ij + β v_j)` have exactly one solution, and it is
`presentValue M A P`. -/
theorem eq5_presentValue_unique {S : Type*} [Fintype S] [DecidableEq S] {D : S → Type*}
    (M : UncertainMDP S D) (A : Policy S D) (P : Sel M) :
    SolvesEq5 M A P (presentValue M A P) ∧
      ∀ v : S → ℝ, SolvesEq5 M A P v → v = presentValue M A P := by sorry

end SatiaLave.MaxMin
