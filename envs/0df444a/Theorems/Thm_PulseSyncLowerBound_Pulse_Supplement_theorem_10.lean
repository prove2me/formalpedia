-- Prove2me | Theorems.Thm_PulseSyncLowerBound_Pulse_Supplement_theorem_10
-- name    : PulseSyncLowerBound.Pulse.Supplement.theorem_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:30:32.698138+00:00
-- url     : https://prove2.me/theorems/009ed2f1-397f-4d4d-baf9-7edb21406d96
-- title:
--   Theorem 10 — exact non-trivial counting needs more than f rounds
-- statement:
--   Let $q,f,n\in\mathbb N$ with $q\ge2$, $f>0$ and $n>f+1$. There is no deterministic finite-state protocol for $f$-resilient **exact non-trivial $q$-counting**, i.e. non-trivial $\sigma$-approximate $q$-counting with skew $\sigma=0$ (Definitions 4 and 5), that stabilises in
--
--   $$T=f\text{ rounds}.$$
--
--   Here the protocol must satisfy:
--
--   1. (N1) every execution with at most $f$ crashes, from any initial configuration, has a $0$-lift of the outputs from round $f$ onwards: integer values $\varphi^\star(i,t)$ with $\varphi(i,t)=\varphi^\star(i,t)\bmod q$, $\varphi^\star(i,t)=\varphi^\star(j,t)$ for all non-faulty $i,j$, and $0\le\varphi^\star(i,t+1)-\varphi^\star(i,t)<q$, for all $t\ge f$;
--   2. (N2) in some crash-free execution, the output of some process changes infinitely often.
--
--   The theorem says these two requirements are incompatible after only $f$ rounds. Compared with the general lower bound (Theorem 6), the skew is $0$, the excluded stabilisation time is $f$ rather than $\lfloor f/2\rfloor$, and the resilience requirement is the weaker $n>f+1$.
--
--   **Formalization Note** The statement uses the published base predicate `CountingResilient P f 0 f` (Definitions 4 and 5) over the published base protocol model; a protocol stabilising in fewer rounds also satisfies the predicate at $T=f$, so smaller stabilisation times are excluded too.
--
--   Differences from the source:
--   - encoding: processes numbered 1 through n with finite local state sets → Fin n identities and arbitrary finite nonempty dependent local state types (the published base model); reason: zero-based relabelling preserves every process, state and execution; finiteness is the paper's model (§2) and nonemptiness its operational state convention
--   - encoding: outputs in Z_q and a 0-lift on non-faulty processes times Z → Fin q outputs and integer lifts on all identities at natural times, constrained only on non-faulty identities and t ≥ f; reason: Fin q is the residue set; unconstrained identities and negative times extend arbitrarily, so every L1–L3 instance is preserved
-- source:
--   Joel Rybicki, STOC 2027 submission #508 (October 2026), pinned published-basis artifact; Theorem 10; PDF p.12 / printed p.10; papers/stoc2027-508/source.pdf; SHA-256 5237f877941c17d0913977954f4f4b6ccba70f65ceae5dc47f15029dbd68765f. Definitions 4–5: PDF p.7 / printed p.5.

import Definitions.Def_PulseSyncLowerBound_Pulse_Tasks

namespace PulseSyncLowerBound.Pulse.Supplement

open PulseSyncLowerBound.Pulse

attribute [local instance] Classical.propDecidable Classical.decEq

theorem theorem_10 {n q f : ℕ} (P : Protocol n (Fin q))
    (hq : 2 ≤ q) (hf : 0 < f) (hn : f + 1 < n) :
    ¬ CountingResilient P f 0 f := by sorry

end PulseSyncLowerBound.Pulse.Supplement
