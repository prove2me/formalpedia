-- Prove2me | Theorems.Thm_PulseSyncLowerBound_Pulse_theorem_2
-- name    : PulseSyncLowerBound.Pulse.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:00:42.004292+00:00
-- url     : https://prove2.me/theorems/4b0f362c-a63c-4d1e-8f90-7ef8ffdf93b1
-- title:
--   Theorem 2 — linear stabilisation lower bound for pulse synchronisation
-- statement:
--   Let $n,f,T\in\mathbb N$, let $\sigma\in\mathbb R$ satisfy $\sigma\ge1$, and suppose $n>f+2$. Every deterministic finite-state $f$-resilient pulse synchronisation protocol of skew $\sigma$ that stabilises in $T$ rounds must satisfy the strict bound
--
--   $$T+2\sigma>\lfloor f/2\rfloor.$$
--
--   The quantification includes all finite nonempty local state spaces, every full initial configuration, and every infinite synchronous execution with at most $f$ total crashes. Stabilisation means the first pulse interval starts by $T$, each non-faulty process pulses exactly once in each interval of width at most $\sigma$, and consecutive intervals are separated by more than $\sigma$ with no intervening pulses. There is no upper frequency bound, and no assumption $f>0$.
--
--   This is an operational impossibility with the source's exact constant, including the small-$f$ cases where its subtracted threshold is negative.
--
--   Differences from the source:
--   - encoding: processes numbered 1 through n with pairwise disjoint finite local state sets (operationally nonempty) → Fin n identities and arbitrary finite nonempty dependent local state types, with identity-tagged states and views; reason: zero-based relabelling and tagged disjoint union preserve every process, state, and execution; nonemptiness is the operational state convention used explicitly in the Lemma 12 proof
--   - reading: Theorem 2 writes sigma>0 without declaring its type, while Definition 1 requires sigma≥1 → use Definition 1’s stated domain sigma≥1; reason: the task is not defined by the source below one; positive integer skews are all included
--   - generalization: the reduction uses the integer modulus q=2sigma+1 → the goal admits every finite real skew sigma≥1; reason: integer interval endpoints give exactly the same pulse predicate at s=floor(sigma); the integer-skew bound T+2s>floor(f/2) implies T+2sigma>floor(f/2)
--   - encoding: no protocol stabilises in floor(f/2)−2sigma rounds → for every natural stabilisation bound T, T+2sigma>floor(f/2) in the reals; reason: the additive strict inequality preserves negative thresholds and monotonicity in the allowed stabilisation time, without truncated natural subtraction
-- source:
--   Joel Rybicki, STOC 2027 submission #508 (October 2026), pinned published-basis artifact; Theorem 2; PDF p.5 / printed p.3; papers/stoc2027-508/source.pdf; SHA-256 5237f877941c17d0913977954f4f4b6ccba70f65ceae5dc47f15029dbd68765f. Repeated and proved PDF p.10 / printed p.8.

import Definitions.Def_PulseSyncLowerBound_Pulse_Tasks

namespace PulseSyncLowerBound.Pulse

attribute [local instance] Classical.propDecidable Classical.decEq

theorem theorem_2 {n f T : ℕ} (σ : ℝ) (P : Protocol n Bool)
    (hσ : 1 ≤ σ) (hn : f + 2 < n) (hP : PulseResilient P f σ T) :
    ((f / 2 : ℕ) : ℝ) < (T : ℝ) + 2 * σ := by sorry

end PulseSyncLowerBound.Pulse
