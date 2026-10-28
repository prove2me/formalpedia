-- Prove2me | Theorems.Thm_RendezvousKn_Sym_eq_6
-- name    : RendezvousKn.Sym.eq_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T04:38:54.741217+00:00
-- url     : https://prove2.me/theorems/28954317-656d-445f-8ab7-1475040366a1
-- title:
--   (6), §3.3, p. 7 (corrected: event π(τ_A(i)) ≠ τ_B(i), not τ_A(π(i)) ≠ τ_B(i)) — P(no rendezvous) = P(X = 0)
-- statement:
--   Fix $n\ge2$ and tactics $\tau_A,\tau_B$; let $F=\{(\tau_A(i),\tau_B(i)):i\in[n]\}$ and let $X=|F\cap E(\pi)|$ be the number of pairs $(i,j)\in F$ with $\pi(i)=j$, for a uniformly random binding $\pi$. Then
--   $$\mathbb P\bigl(\pi(\tau_A(i))\neq\tau_B(i)\ \text{for all } i\in[n]\bigr)=\mathbb P(X=0).\qquad(6)$$
--
--   This identity translates the no-rendezvous event into the vanishing of the match count $X$, whose moments are then analysed.
--
--   Differences from the source:
--   - correction: no-rendezvous event τ_A(π(i)) ≠ τ_B(i) for all i ∈ [n] → event π(τ_A(i)) ≠ τ_B(i) for all i (noRdvProb), the event of the game's definition on p. 3 and of the proof (Z > n); reason: the printed event makes the statement false: n ≥ 2, τ_A ≡ 1, τ_B ≡ 2 gives printed probability 1 (take β = 1) while W = 1/n + (n+1)(1 − 1/n) = n < n + 1/2 and P(X = 0) = 1 − 1/n
--   - encoding: expectation over a uniformly random binding π: [n] → [n]; rounds 1, …, n; locations [n] → average over all n! elements of Equiv.Perm (Fin n) (avgPerm); rounds and locations are Fin n, Lean round i being round i + 1; reason: the same finite uniform distribution and the same game; no instance changes
-- source:
--   Bonamy, Pilipczuk, Sereni, On the effect of symmetry requirement for rendezvous on the complete graph, arXiv:2002.03764v1, p. 7 (PDF 8), §3.3, equation (6)

import Mathlib
import Definitions.Def_RendezvousKn_Sym_Model

namespace RendezvousKn.Sym

theorem eq_6 (n : ℕ) (hn : 2 ≤ n) (τA τB : Tactic n) :
    noRdvProb τA τB = probXZero (pairSet τA τB) := by sorry

end RendezvousKn.Sym
