-- Prove2me | Theorems.Thm_PulseSyncLowerBound_Pulse_theorem_6
-- name    : PulseSyncLowerBound.Pulse.theorem_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:00:29.045477+00:00
-- url     : https://prove2.me/theorems/1eff27b0-a597-4867-9f0c-6d9f1df94a4e
-- title:
--   Theorem 6 — non-trivial counting lower bound
-- statement:
--   Let $\sigma,q,f,n\in\mathbb N$ with $q>\max\{2\sigma,1\}$, $n>f+2$, and $f>0$. There is no deterministic finite-state protocol for $f$-resilient non-trivial $\sigma$-approximate $q$-counting that stabilises in
--
--   $$T=\lfloor f/2\rfloor\text{ rounds}.$$
--
--   The protocol must handle every full initial configuration and every infinite execution with at most $f$ total crashes. Non-trivial counting requires N1 in all such executions and N2 in one crash-free execution for one process. The skew $\sigma=0$ is retained. This is the exact counting impossibility used by the pulse lower bound.
--
--   Differences from the source:
--   - encoding: processes numbered 1 through n with pairwise disjoint finite local state sets (operationally nonempty) → Fin n identities and arbitrary finite nonempty dependent local state types, with identity-tagged states and views; reason: zero-based relabelling and tagged disjoint union preserve every process, state, and execution; nonemptiness is the operational state convention used explicitly in the Lemma 12 proof
--   - encoding: outputs in Zq and lifts on non-faulty processes times Z → Fin q outputs and integer lifts on all identities at natural times, constrained only on non-faulty identities and t at least T; reason: Fin q is exactly the residue-label set; unconstrained identities and negative times extend arbitrarily, so all L1--L3 instances are preserved
-- source:
--   Joel Rybicki, STOC 2027 submission #508 (October 2026), pinned published-basis artifact; Theorem 6; PDF p.25 / printed p.23; papers/stoc2027-508/source.pdf; SHA-256 5237f877941c17d0913977954f4f4b6ccba70f65ceae5dc47f15029dbd68765f. Also stated PDF p.8 / printed p.6.

import Definitions.Def_PulseSyncLowerBound_Pulse_Tasks

namespace PulseSyncLowerBound.Pulse

attribute [local instance] Classical.propDecidable Classical.decEq

theorem theorem_6 {n q f σ : ℕ} (P : Protocol n (Fin q))
    (hq : max (2 * σ) 1 < q) (hn : f + 2 < n) (hf : 0 < f) :
    ¬ CountingResilient P f σ (f / 2) := by sorry

end PulseSyncLowerBound.Pulse
