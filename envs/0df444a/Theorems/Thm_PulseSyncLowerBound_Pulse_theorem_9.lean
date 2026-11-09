-- Prove2me | Theorems.Thm_PulseSyncLowerBound_Pulse_theorem_9
-- name    : PulseSyncLowerBound.Pulse.theorem_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:00:53.296599+00:00
-- url     : https://prove2.me/theorems/84daaa9d-9a53-4be4-afe5-de4cd6d99357
-- title:
--   Theorem 9 — full-information connectivity
-- statement:
--   Let $\mathcal A$ be a finite-state synchronous protocol on $n$ processes with arbitrary nonempty local state spaces and all full configurations initially allowed. For every $r,k\in\mathbb N$ with $n>(r+1)k$, the full-information protocol complex satisfies
--
--   $$R(r,k)\text{ is homotopically }(k-1)\text{-connected}.$$
--
--   At $k=0$ this means nonempty. At every larger $k$, every homotopy group of its geometric realization in degrees $0$ through $k-1$ is trivial. This retains the entire connectivity theorem attributed in the source to Herlihy, Rajsbaum and Tuttle, rather than only its two later applications.
--
--   Differences from the source:
--   - encoding: processes numbered 1 through n with pairwise disjoint finite local state sets (operationally nonempty) → Fin n identities and arbitrary finite nonempty dependent local state types, with identity-tagged states and views; reason: zero-based relabelling and tagged disjoint union preserve every process, state, and execution; nonemptiness is the operational state convention used explicitly in the Lemma 12 proof
--   - encoding: homotopical (k−1)-connectivity → nonempty geometric realization and Subsingleton homotopy groups in all natural degrees j<k; reason: the index shift avoids truncated natural subtraction; Mathlib degree zero is the set of path components
-- source:
--   Joel Rybicki, STOC 2027 submission #508 (October 2026), pinned published-basis artifact; Theorem 9; PDF p.12 / printed p.10; papers/stoc2027-508/source.pdf; SHA-256 5237f877941c17d0913977954f4f4b6ccba70f65ceae5dc47f15029dbd68765f.

import Definitions.Def_PulseSyncLowerBound_Pulse_Views

namespace PulseSyncLowerBound.Pulse

attribute [local instance] Classical.propDecidable Classical.decEq

theorem theorem_9 {n : ℕ} {O : Type} (P : Protocol n O) (r k : ℕ)
    (h : (r + 1) * k < n) : ConnectedThrough (RoundComplex P r k) k := by sorry

end PulseSyncLowerBound.Pulse
