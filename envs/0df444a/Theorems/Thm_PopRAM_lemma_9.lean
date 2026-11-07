-- Prove2me | Theorems.Thm_PopRAM_lemma_9
-- name    : PopRAM.lemma_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:28:30.623825+00:00
-- url     : https://prove2.me/theorems/6ac324fb-6a7a-44f1-9bf0-d0321d90e9f3
-- title:
--   Lemma 9 — ranked duels elect a unique leader in expected $O(n)$ time; only it reaches the top rank, at most $1+\lfloor\log n\rfloor$
-- statement:
--   There is a universal constant $K$ such that for every $n\ge2$ and every initial configuration in which each agent is a rank-1 leader or an input agent, with at least one leader:
--
--   1. a configuration with exactly one leader is reached with probability $1$, and the expected number of interactions until then is at most $K\,n^2$ (time $O(n)$);
--   2. on every schedule and at every time, every leader and every follower has rank at most $1+\lfloor\log_2 n\rfloor$;
--   3. on every schedule, if at time $t$ agent $a$ is the only leader, with rank $r$, then every other agent that is a leader at any time $s$ has rank smaller than $r$ at that time, and every follower at any time has rank at most $r$.
--
--   Clause 3 is "only this leader reaches the highest rank in the population": no other agent ever holds the leader role with the final rank, and no follower exceeds it. It is what lets the last leader's simulation overwrite all others without it ever learning that it is unique.
--
--   Differences from the source:
--   - reading: the duel rules, 'Rules involving the leader apply in both interaction orientations' (p.30) → both rules in both orientations; the initiator wins an equal-rank duel; reason: the paper does not say which agent wins an equal-rank duel; the statement holds for either choice
--   - encoding: 'Only this leader reaches the highest rank in the population' → clause 3: every other agent that is ever a leader has a smaller rank then, and every follower has rank at most the final one; reason: the rank is reached as a leader; the duel rules give followers the winner's rank, so a follower may equal it
--   - encoding: expected time O(n) → expected K·n² interactions with K universal; reason: time = interactions / n
-- source:
--   Gąsieniec, Grodzicki, Stachowiak, Efficient Stable Word-RAM Simulation by Population Protocols, arXiv:2611.06178 (preprint, held version, sha256 f13223b33593e77d2342fbfab2d49c58efd6035c06f316456f76030e0dca9acd), Lemma 9 and the duel rules, p.31 (PDF p.32)

import Mathlib
import Definitions.Def_PopRAM_Protocol
import Definitions.Def_PopRAM_Duels

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace PopRAM

/-- **Lemma 9** with the duel rules (Gąsieniec, Grodzicki, Stachowiak, arXiv:2611.06178, held
version sha256 f13223b3…, p.31, PDF p.32). "The leader election and rank computation stage of the
backup simulation elects a unique leader in expected time O(n). Only this leader reaches the highest
rank in the population, which is at most 1 + ⌊log n⌋."

There is a universal `K` such that for every `n ≥ 2` and every initial configuration in which every
agent is a rank-1 leader or an input agent, and at least one is a leader:
1. a configuration with exactly one leader is reached with probability `1`, in expected at most
   `K·n·n` interactions (time `O(n)`);
2. on every schedule and at every time, every leader and every follower has rank at most
   `1 + ⌊log₂ n⌋`;
3. on every schedule, if at time `t` agent `a` is the only leader and has rank `r`, then every other
   agent that is a leader at any time `s` has rank `< r` then, and every follower at any time has
   rank `≤ r`.

**Formalization Note** Clause 3 is "Only this leader reaches the highest rank in the population": no
other agent ever holds the leader role with the final rank or a higher one, and no follower's rank
exceeds it (the duel rules give followers the rank of the winner, so a follower can equal it). -/
theorem lemma_9 :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n → ∀ c₀ : Fin n → DState,
      (∀ b, c₀ b = .ldr 1 ∨ c₀ b = .inp) → (∃ b, c₀ b = .ldr 1) →
      (sched n {ω | hit duelδ c₀ uniqueLeader ω = ⊤} = 0 ∧
        ∫⁻ ω, (hit duelδ c₀ uniqueLeader ω : ℝ≥0∞) ∂(sched n) ≤ ((K * n * n : ℕ) : ℝ≥0∞)) ∧
      (∀ ω t b i, (run duelδ c₀ ω t b = .ldr i ∨ run duelδ c₀ ω t b = .fol i) →
        i ≤ 1 + Nat.log 2 n) ∧
      (∀ ω t (a : Fin n) (r : ℕ), (∀ b, isLdr (run duelδ c₀ ω t b) = true ↔ b = a) →
        run duelδ c₀ ω t a = .ldr r →
        ∀ s (b : Fin n) (r' : ℕ),
          (b ≠ a → run duelδ c₀ ω s b = .ldr r' → r' < r) ∧
          (run duelδ c₀ ω s b = .fol r' → r' ≤ r)) := by sorry

end PopRAM
