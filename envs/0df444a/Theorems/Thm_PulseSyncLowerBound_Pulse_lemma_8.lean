-- Prove2me | Theorems.Thm_PulseSyncLowerBound_Pulse_lemma_8
-- name    : PulseSyncLowerBound.Pulse.lemma_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:01:37.698831+00:00
-- url     : https://prove2.me/theorems/ced4bece-3ba9-4303-8891-01f5eedc7a01
-- title:
--   Lemma 8 — pulse-to-counting lift
-- statement:
--   Let $n,f,T\in\mathbb N$, let $\sigma$ be a positive integer, and let $\mathcal A$ be an $f$-resilient pulse protocol with skew $\sigma$ stabilising in $T$ rounds. Form the augmented counter protocol of Section 2.3 with modulus $q=2\sigma+1$. Every execution of that particular protocol with at most $f$ total crashes has a $\sigma$-lift from round
--
--   $$T+2\sigma.$$
--
--   The claim includes compatibility, skew agreement, and nondecreasing increments strictly smaller than $q$ for every non-faulty process. It supplies the universal-lift component of the reduction.
--
--   Differences from the source:
--   - encoding: processes numbered 1 through n with pairwise disjoint finite local state sets (operationally nonempty) → Fin n identities and arbitrary finite nonempty dependent local state types, with identity-tagged states and views; reason: zero-based relabelling and tagged disjoint union preserve every process, state, and execution; nonemptiness is the operational state convention used explicitly in the Lemma 12 proof
--   - encoding: outputs in Zq and lifts on non-faulty processes times Z → Fin q outputs and integer lifts on all identities at natural times, constrained only on non-faulty identities and t at least T; reason: Fin q is exactly the residue-label set; unconstrained identities and negative times extend arbitrarily, so all L1--L3 instances are preserved
-- source:
--   Joel Rybicki, STOC 2027 submission #508 (October 2026), pinned published-basis artifact; Lemma 8; PDF p.9 / printed p.7; papers/stoc2027-508/source.pdf; SHA-256 5237f877941c17d0913977954f4f4b6ccba70f65ceae5dc47f15029dbd68765f.

import Definitions.Def_PulseSyncLowerBound_Pulse_Counter

namespace PulseSyncLowerBound.Pulse

attribute [local instance] Classical.propDecidable Classical.decEq

theorem lemma_8 {n f σ T : ℕ} (P : Protocol n Bool)
    (hσ : 0 < σ) (hP : PulseResilient P f (σ : ℝ) T)
    (e : Execution (counterProtocol P σ)) (he : AtMostCrashes e f) :
    HasLift e σ (T + 2 * σ) := by sorry

end PulseSyncLowerBound.Pulse
