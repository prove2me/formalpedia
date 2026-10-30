-- Prove2me | Theorems.Thm_RendezvousKn_Sym_eq_1
-- name    : RendezvousKn.Sym.eq_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T04:38:54.020781+00:00
-- url     : https://prove2.me/theorems/9c2673dc-0bd6-42d8-9b04-6d10295d2aca
-- title:
--   (1), proof of Theorem 1, p. 4 — W(τ_A, τ_B) ≥ (n+1)/2 for all tactics
-- statement:
--   Fix $n\ge 2$. For all tactics $\tau_A,\tau_B:[n]\to[n]$, the expected waiting time over the uniformly random binding satisfies
--   $$W(\tau_A,\tau_B)\ \ge\ \frac{n+1}{2}.$$
--
--   This is Theorem 2 for two deterministic strategies; it bounds the cross terms between passive and active tactics in the proof of Theorem 1.
--
--   **Formalization Note** The hypothesis $n\ge2$ is §3's standing assumption ('we fix the number of locations n to be at least 2', p. 3).
--
--   Differences from the source:
--   - encoding: expectation over a uniformly random binding π: [n] → [n]; rounds 1, …, n; locations [n] → average over all n! elements of Equiv.Perm (Fin n) (avgPerm); rounds and locations are Fin n, Lean round i being round i + 1; reason: the same finite uniform distribution and the same game; no instance changes
-- source:
--   Bonamy, Pilipczuk, Sereni, On the effect of symmetry requirement for rendezvous on the complete graph, arXiv:2002.03764v1, p. 4 (PDF 5), proof of Theorem 1, equation (1)

import Mathlib
import Definitions.Def_RendezvousKn_Sym_Model

namespace RendezvousKn.Sym

theorem eq_1 (n : ℕ) (hn : 2 ≤ n) (τA τB : Tactic n) :
    ((n : ℝ) + 1) / 2 ≤ W τA τB := by sorry

end RendezvousKn.Sym
