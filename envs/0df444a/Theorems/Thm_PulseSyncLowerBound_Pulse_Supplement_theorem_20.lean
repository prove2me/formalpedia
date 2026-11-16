-- Prove2me | Theorems.Thm_PulseSyncLowerBound_Pulse_Supplement_theorem_20
-- name    : PulseSyncLowerBound.Pulse.Supplement.theorem_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:31:01.699511+00:00
-- url     : https://prove2.me/theorems/dd965209-377f-42b3-b4d0-ed3ecb556a4e
-- title:
--   Theorem 20 — 1-approximate q-counting in ⌈f/2⌉ + ⌈log₂ q⌉ − 1 rounds
-- statement:
--   Let $q\ge4$ and let $n\in\mathbb N$ be the number of processes. There is a deterministic finite-state protocol in the synchronous crash-fault model which, for every $f\in\mathbb N$, is an $f$-resilient $1$-approximate $q$-counting protocol (Definition 3) that stabilises by round
--
--   $$T_f=\left\lceil \frac f2\right\rceil+\lceil\log_2 q\rceil-1 .$$
--
--   That is, in every execution with at most $f$ crashes, starting from an arbitrary initial configuration, for every round $t\ge T_f$:
--
--   1. (A1) the outputs of the non-faulty processes lie on a $1$-path $\{c, c+1 \bmod q\}$ of the $q$-cycle;
--   2. (A2) every non-faulty process increases its output by exactly $1$ modulo $q$ from round $t$ to round $t+1$.
--
--   No relation between $n$ and $f$ is assumed. For $q=4$ the bound is $\lceil f/2\rceil+1$, which matches the lower bound of Corollary 7 for every even $f>0$.
--
--   **Formalization Note** $\lceil f/2\rceil$ is written $(f+1)/2$ in $\mathbb N$ and $\lceil\log_2 q\rceil$ is `Nat.clog 2 q`; both are the exact ceilings. The natural subtraction of $1$ never truncates, since `Nat.clog 2 q` $\ge 2$ for $q\ge4$. The protocol may use any finite nonempty local state sets of the base model.
--
--   Differences from the source:
--   - generalization: for each f there is an f-resilient protocol stabilising by round ⌈f/2⌉+⌈log₂ q⌉−1 → one protocol (for given n, q) that is f-resilient with that bound simultaneously for every f; reason: the §7.1 protocol does not depend on f, and instantiating the universal f gives the source's statement for each f
--   - encoding: processes numbered 1 through n with finite local state sets → Fin n identities and arbitrary finite nonempty dependent local state types (the published base model); reason: zero-based relabelling preserves every process, state and execution; the source's protocol has state set Z_q, which is finite and nonempty for q ≥ 4
--   - encoding: ⌈f/2⌉ and ⌈log₂ q⌉ → (f + 1) / 2 and Nat.clog 2 q in ℕ; reason: exact ceilings for all f and all q ≥ 1; the subtraction of 1 is not truncated because Nat.clog 2 q ≥ 2 for q ≥ 4
-- source:
--   Joel Rybicki, STOC 2027 submission #508 (October 2026), pinned published-basis artifact; Theorem 20; PDF p.27 / printed p.25 (protocol and Lemmas 18–19: PDF pp.26–27 / printed pp.24–25); papers/stoc2027-508/source.pdf; SHA-256 5237f877941c17d0913977954f4f4b6ccba70f65ceae5dc47f15029dbd68765f. Definition 3: PDF p.6 / printed p.4.

import Definitions.Def_PulseSyncLowerBound_Pulse_Supplement_ApproxCounting

namespace PulseSyncLowerBound.Pulse.Supplement

open PulseSyncLowerBound.Pulse

attribute [local instance] Classical.propDecidable Classical.decEq

theorem theorem_20 (n q : ℕ) (hq : 4 ≤ q) :
    ∃ P : Protocol n (Fin q), ∀ f : ℕ,
      ApproxCountingResilient P f 1 ((f + 1) / 2 + Nat.clog 2 q - 1) := by sorry

end PulseSyncLowerBound.Pulse.Supplement
