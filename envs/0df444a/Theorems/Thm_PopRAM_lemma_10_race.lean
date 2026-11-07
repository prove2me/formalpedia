-- Prove2me | Theorems.Thm_PopRAM_lemma_10_race
-- name    : PopRAM.lemma_10_race
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:26:11.070097+00:00
-- url     : https://prove2.me/theorems/3118b427-9bc5-4ef1-8192-c71055d36664
-- title:
--   Proof of Lemma 10 — the helper race: $A$ meets $H$ $m$ times before $b$ with probability $2^{-m}$; union bound $N2^{-m}$
-- statement:
--   Let $n\ge3$, let $A$ (the leader) and $H$ (the helper) be distinct agents, and $m\in\mathbb N$. Under the uniform random scheduler, counting interactions in either orientation as meetings:
--
--   1. for every agent $b\notin\{A,H\}$, the probability that $A$ meets $H$ at least $m$ times before its first meeting with $b$ is exactly $2^{-m}$;
--   2. for every set $B$ of agents not containing $A$ or $H$, the probability that this happens for some $b\in B$ is at most $|B|\,2^{-m}$.
--
--   With $m=dw$ and $B$ the $N$ uncounted input agents, this bounds the probability that the backup's input conversion misses an input agent by $N2^{-dw}$.
--
--   Differences from the source:
--   - encoding: meetings of the leader in the waiting state, with the scan paused during register increments → all meetings of A on the bare scheduler; reason: the paper observes that pausing does not change the symmetry; on the bare scheduler the race is the same
--   - generalization: m = dw and B the N uncounted input agents → every m ∈ ℕ and every set B disjoint from {A, H}; reason: the paper's case is an instance
-- source:
--   Gąsieniec, Grodzicki, Stachowiak, Efficient Stable Word-RAM Simulation by Population Protocols, arXiv:2611.06178 (preprint, held version, sha256 f13223b33593e77d2342fbfab2d49c58efd6035c06f316456f76030e0dca9acd), proof of Lemma 10, p.34 (PDF p.35)

import Mathlib
import Definitions.Def_PopRAM_Meeting

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace PopRAM

/-- **Proof of Lemma 10, the helper race** (Gąsieniec, Grodzicki, Stachowiak, arXiv:2611.06178,
held version sha256 f13223b3…, p.34, PDF p.35). "Until B is counted, the probabilities of meeting B
and the helper are equal. Pausing the scan during register increments does not change this symmetry.
Hence the probability of meeting the helper dw times before meeting B is 2^{−dw}. A union bound over
the N uncounted input agents gives N2^{−dw}."

On `n ≥ 3` agents, let `A` (the leader) and `H` (the helper) be distinct agents and `m ∈ ℕ`.
1. For every agent `b ∉ {A, H}`, the probability that `A` meets `H` `m` times before it first meets
   `b` is exactly `2^{-m}`.
2. For every set `B` of agents not containing `A` or `H`, the probability that this happens for some
   `b ∈ B` is at most `|B|·2^{-m}`.

**Formalization Note** Stated on the bare scheduler: a meeting is an interaction of the two agents
in either orientation. The paper's `m = dw` and `B` = the `N` uncounted input agents. -/
theorem lemma_10_race (n : ℕ) (hn : 3 ≤ n) (A H : Fin n) (hAH : A ≠ H) (m : ℕ) :
    (∀ b : Fin n, b ≠ A → b ≠ H → sched n {ω | HelperFirst A H b m ω} = (2 ^ m : ℝ≥0∞)⁻¹) ∧
    ∀ B : Finset (Fin n), A ∉ B → H ∉ B →
      sched n {ω | ∃ b ∈ B, HelperFirst A H b m ω} ≤ (B.card : ℝ≥0∞) * (2 ^ m : ℝ≥0∞)⁻¹ := by sorry

end PopRAM
