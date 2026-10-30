-- Prove2me | Theorems.Thm_RendezvousKn_Sym_theorem_2
-- name    : RendezvousKn.Sym.theorem_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T04:38:50.84098+00:00
-- url     : https://prove2.me/theorems/54dae974-538f-462c-aee7-982337d40f43
-- title:
--   Theorem 2 (Anderson–Weber), p. 3 — every pair of strategies has E T⟨σ_A, σ_B⟩ ≥ (n+1)/2 in the game stopped after n rounds
-- statement:
--   Consider the rendezvous game on $n$ locations of §2: tactics $\tau:[n]\to[n]$, a uniformly random binding $\pi$, and the waiting time $T$ equal to the first round $i\le n$ with $\pi(\tau_A(i))=\tau_B(i)$, or $n+1$ if the players never meet. For every $n\in\mathbb N$ and every pair of strategies $\sigma_A,\sigma_B$ (probability vectors on tactics),
--   $$\mathbb E\,T\langle\sigma_A,\sigma_B\rangle\ \ge\ \frac{n+1}{2}.$$
--
--   This is the Anderson–Weber lower bound, valid with no symmetry constraint; the wait-for-mommy pair (one player stays at one location, the other visits all locations once) attains it. The paper remarks that its proof also holds for the game stopped after round $n$, which is the game of this mission.
--
--   **Formalization Note** For $n=0$ there is one tactic and one binding, and $T=1\ge 1/2$.
--
--   Differences from the source:
--   - reading: Theorem 2 as cited from Anderson and Weber, with the remark that its proof also holds for the game stopped after round n → stated for the game of §2, stopped after n rounds with T = n + 1 when the players never meet; reason: the paper uses Theorem 2 only for this game, and says the bound holds for it
--   - encoding: strategy σ ∈ Σ_n, a probability distribution on the tactics [n] → [n]; E T⟨σ_A, σ_B⟩ with independent draws → σ ∈ stdSimplex ℝ (Fin n → Fin n); expWait σ_A σ_B = Σ_{τ_A, τ_B} σ_A(τ_A) σ_B(τ_B) W(τ_A, τ_B); reason: a distribution on a finite set is its probability vector; the double sum is the expectation over independent τ_A ~ σ_A, τ_B ~ σ_B, π uniform (the paper's E T⟨σ_A, σ_B⟩ = Φ⟨a, b⟩, p. 4)
--   - encoding: expectation over a uniformly random binding π: [n] → [n]; rounds 1, …, n; locations [n] → average over all n! elements of Equiv.Perm (Fin n) (avgPerm); rounds and locations are Fin n, Lean round i being round i + 1; reason: the same finite uniform distribution and the same game; no instance changes
-- source:
--   Bonamy, Pilipczuk, Sereni, On the effect of symmetry requirement for rendezvous on the complete graph, arXiv:2002.03764v1, p. 3 (PDF 4), Theorem 2 and the sentence before it ('the proof of this result also holds for the game stopped after round n')

import Mathlib
import Definitions.Def_RendezvousKn_Sym_Model

namespace RendezvousKn.Sym

theorem theorem_2 (n : ℕ) (σA σB : Tactic n → ℝ)
    (hσA : σA ∈ stdSimplex ℝ (Tactic n)) (hσB : σB ∈ stdSimplex ℝ (Tactic n)) :
    ((n : ℝ) + 1) / 2 ≤ expWait σA σB := by sorry

end RendezvousKn.Sym
