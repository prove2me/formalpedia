-- Prove2me | Theorems.Thm_RendezvousKn_Sym_assertion_2
-- name    : RendezvousKn.Sym.assertion_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T04:39:00.798603+00:00
-- url     : https://prove2.me/theorems/1348a9c4-269d-4219-a22e-5cb2bba29d61
-- title:
--   Assertion 2, p. 8 — E X⁴ ≤ 15
-- statement:
--   Fix $n\ge2$, tactics $\tau_A,\tau_B$, the pair set $F=\{(\tau_A(i),\tau_B(i)):i\in[n]\}$, and the match count $X=|\{(i,j)\in F:\pi(i)=j\}|$ for a uniformly random binding $\pi$. Then
--   $$\mathbb E\,X^4\ \le\ 15.$$
--
--   The bound is uniform in $n$ and in the tactics, and controls the fourth central moment of $X$ in the proof of Lemma 6.
--
--   Differences from the source:
--   - encoding: expectation over a uniformly random binding π: [n] → [n]; rounds 1, …, n; locations [n] → average over all n! elements of Equiv.Perm (Fin n) (avgPerm); rounds and locations are Fin n, Lean round i being round i + 1; reason: the same finite uniform distribution and the same game; no instance changes
-- source:
--   Bonamy, Pilipczuk, Sereni, On the effect of symmetry requirement for rendezvous on the complete graph, arXiv:2002.03764v1, p. 8 (PDF 9), Assertion 2

import Mathlib
import Definitions.Def_RendezvousKn_Sym_Model

namespace RendezvousKn.Sym

theorem assertion_2 (n : ℕ) (hn : 2 ≤ n) (τA τB : Tactic n) :
    avgPerm n (fun π => (matchCount (pairSet τA τB) π : ℝ) ^ 4) ≤ 15 := by sorry

end RendezvousKn.Sym
