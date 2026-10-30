-- Prove2me | Theorems.Thm_RendezvousKn_Sym_lemma_5
-- name    : RendezvousKn.Sym.lemma_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T04:38:59.578351+00:00
-- url     : https://prove2.me/theorems/95a4f428-78e7-46dd-a89c-1dd5dacdc9f0
-- title:
--   Lemma 5, p. 5 (corrected: event π(τ_A(i)) ≠ τ_B(i), not τ_A(π(i)) ≠ τ_B(i)) — no-rendezvous probability ≥ β gives W ≥ (n+1)/2 + (β²/2)n
-- statement:
--   Fix $n\ge2$ and tactics $\tau_A,\tau_B$. Suppose that, for a uniformly random binding $\pi$, the probability that no rendezvous occurs in the $n$ rounds satisfies
--   $$\mathbb P\bigl(\pi(\tau_A(i))\neq\tau_B(i)\ \text{for all } i\in[n]\bigr)\ \ge\ \beta$$
--   for some constant $\beta>0$. Then
--   $$W(\tau_A,\tau_B)\ \ge\ \frac{n+1}{2}+\frac{\beta^2}{2}\,n.$$
--
--   A constant probability of never meeting thus raises the expected waiting time by a linear amount above the Anderson–Weber bound; this reduces Lemma 4 to a lower bound on the no-rendezvous probability.
--
--   Differences from the source:
--   - correction: no-rendezvous event τ_A(π(i)) ≠ τ_B(i) for all i ∈ [n] → event π(τ_A(i)) ≠ τ_B(i) for all i (noRdvProb), the event of the game's definition on p. 3 and of the proof (Z > n); reason: the printed event makes the statement false: n ≥ 2, τ_A ≡ 1, τ_B ≡ 2 gives printed probability 1 (take β = 1) while W = 1/n + (n+1)(1 − 1/n) = n < n + 1/2 and P(X = 0) = 1 − 1/n
--   - encoding: expectation over a uniformly random binding π: [n] → [n]; rounds 1, …, n; locations [n] → average over all n! elements of Equiv.Perm (Fin n) (avgPerm); rounds and locations are Fin n, Lean round i being round i + 1; reason: the same finite uniform distribution and the same game; no instance changes
-- source:
--   Bonamy, Pilipczuk, Sereni, On the effect of symmetry requirement for rendezvous on the complete graph, arXiv:2002.03764v1, p. 5 (PDF 6), Lemma 5 (proof p. 6, PDF 7)

import Mathlib
import Definitions.Def_RendezvousKn_Sym_Model

namespace RendezvousKn.Sym

theorem lemma_5 (n : ℕ) (hn : 2 ≤ n) (τA τB : Tactic n) (β : ℝ) (hβ : 0 < β)
    (hprob : β ≤ noRdvProb τA τB) :
    ((n : ℝ) + 1) / 2 + β ^ 2 / 2 * n ≤ W τA τB := by sorry

end RendezvousKn.Sym
