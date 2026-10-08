-- Prove2me | Theorems.Thm_RunwayCPS_DiscreteTime_theorem_1
-- name    : RunwayCPS.DiscreteTime.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:16:14.794738+00:00
-- url     : https://prove2.me/theorems/800c0f4f-3277-4fd8-bbb1-876c96c79952
-- title:
--   Theorem 1 — CPS sequences respecting precedence are exactly the sequences of source-sink paths of the pruned CPS network
-- statement:
--   Let $G$ be the precedence-pruned CPS network of an instance with $n\ge 1$ aircraft and maximum shift $k$. For every sequence $\sigma$ of the aircraft,
--   $$
--   \sigma \text{ is } k\text{-CPS and respects every precedence pair}
--   \iff
--   \sigma \text{ is the sequence of some source-sink path of } G ,
--   $$
--   where the sequence of a path places the final aircraft of its stage-$p$ node in position $p$.
--
--   This is Theorem 1 of the paper together with Lemmas 1 and 2 of §3.1, which show that pruning the nodes that violate a precedence pair removes exactly the paths whose sequences violate it. Every network of §6 is built on $G$, so this theorem is what makes their paths correspond to sequences.
--
--   **Formalization Note** The paper states the result for the unpruned network; the precedence version is the content of §3.1. Aircraft and positions are $0$-based, stages $1$-based.
-- source:
--   Balakrishnan & Chandran, Algorithms for Scheduling Runway Operations Under Constrained Position Shifting, Oper. Res. 58(6) (2010), pp. 1652–1653, Theorem 1; pp. 1653–1654, Lemmas 1 and 2

import Mathlib
import Definitions.Def_RunwayCPS_DiscreteTime_Network

namespace RunwayCPS.DiscreteTime

/-- Theorem 1 (pp. 1652–1653), for the precedence-pruned network `G` of §3.1: a sequence `σ`
is a `k`-CPS sequence respecting the precedence constraints if and only if it is the aircraft
sequence of a source-sink path of `G`. -/
theorem theorem_1 {n : ℕ} [NeZero n] (I : Instance n) (σ : Fin n → Fin n) :
    (RunwayCPS.Makespan.IsCPS I.k σ ∧ RunwayCPS.Makespan.RespectsPrec I.prec σ) ↔
      ∃ v : ℕ → List (Fin n), IsGPath I v ∧ RunwayCPS.Makespan.pathSeq v = σ := by sorry

end RunwayCPS.DiscreteTime
