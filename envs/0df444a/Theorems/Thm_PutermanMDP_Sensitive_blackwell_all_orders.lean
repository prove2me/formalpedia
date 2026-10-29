-- Prove2me | Theorems.Thm_PutermanMDP_Sensitive_blackwell_all_orders
-- name    : PutermanMDP.Sensitive.blackwell_all_orders
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T02:33:02.878243+00:00
-- url     : https://prove2.me/theorems/0125a79c-f2f9-4b26-a30e-cf2fad6bea46
-- title:
--   Theorem 10.1.5 — existence and all finite sensitivity orders
-- statement:
--   In a finite-state, finite-action Markov decision process, for each integer $n\ge-1$ there exists a stationary deterministic $n$-discount optimal policy. Moreover every stationary deterministic Blackwell optimal policy is $n$-discount optimal for every such $n$:
--   $$\forall n\ge-1,\ \exists d,\ d^\infty\text{ is }n\text{-discount optimal},$$
--   $$d^\infty\text{ Blackwell optimal}\ \Longrightarrow\ \forall n\ge-1,\ d^\infty\text{ is }n\text{-discount optimal}.$$
--   Both optimality notions compare against every history-dependent randomized policy. This theorem establishes existence at every sensitivity level and the easy direction of the relation with Blackwell optimality.
-- source:
--   Puterman, Markov Decision Processes, Wiley, 1994, p. 496 (PDF 512), Theorem 10.1.5; https://doi.org/10.1002/9780470316887

import Mathlib
import Definitions.Def_PutermanMDP_Sensitive_Model

namespace PutermanMDP.Sensitive

theorem blackwell_all_orders {S A : Type} [Fintype S] [DecidableEq S] [Nonempty S] [Fintype A]
    (M : Model S A) :
    (∀ n : ℤ, -1 ≤ n → ∃ d : DecisionRule M, NDiscountOptimal (stationary d) n) ∧
    (∀ d : DecisionRule M, BlackwellOptimal (stationary d) →
      ∀ n : ℤ, -1 ≤ n → NDiscountOptimal (stationary d) n) := by sorry

end PutermanMDP.Sensitive
