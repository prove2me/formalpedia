-- Prove2me | Theorems.Thm_RendezvousKn_Sym_theorem_1
-- name    : RendezvousKn.Sym.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:39:16.388985+00:00
-- url     : https://prove2.me/theorems/34cbc71a-5213-45ee-aba3-a0fd709b249e
-- title:
--   Theorem 1, p. 3 — symmetric strategies have expected rendezvous time at least (n+1)/2 + 2⁻³⁶n for every n ≥ 2
-- statement:
--   In the rendezvous game on $n$ locations, both players must use the **same** strategy $\sigma$, a probability distribution on the tactics $[n]\to[n]$; they draw their tactics independently from $\sigma$, and the binding $\pi$ is a uniformly random permutation independent of both. The waiting time $T$ is the first round $i\le n$ in which they stand at the same location, or $n+1$ if they never meet. For every $n\ge2$ and every strategy $\sigma\in\Sigma_n$,
--   $$\mathbb E\,T\langle\sigma,\sigma\rangle\ \ge\ \frac{n+1}{2}+2^{-36}\,n.$$
--
--   Without the symmetry constraint the optimal value is exactly $(n+1)/2$ (Anderson–Weber, attained by wait-for-mommy). The theorem shows that requiring both players to use the same strategy costs a linear number of additional rounds, with a constant independent of $n$.
--
--   **Formalization Note** The paper states "there exists $\varepsilon>0$ such that for every $n\ge2$", and its conclusion (p. 12) gives $\varepsilon=2^{-36}$; the Lean statement uses this constant. One strategy vector $\sigma$ enters both arguments of `expWait`, and it ranges over all probability vectors on all $n^n$ tactics.
--
--   Differences from the source:
--   - generalization: there exists ε > 0 such that for every n ≥ 2 … → ε = 2⁻³⁶; reason: the paper's own constant (abstract; p. 12: 'Theorem 1 holds for ε = 2⁻³⁶'); the explicit constant implies the existential, uniformly in n
--   - encoding: strategy σ ∈ Σ_n, a probability distribution on the tactics [n] → [n]; E T⟨σ_A, σ_B⟩ with independent draws → σ ∈ stdSimplex ℝ (Fin n → Fin n); expWait σ_A σ_B = Σ_{τ_A, τ_B} σ_A(τ_A) σ_B(τ_B) W(τ_A, τ_B); reason: a distribution on a finite set is its probability vector; the double sum is the expectation over independent τ_A ~ σ_A, τ_B ~ σ_B, π uniform (the paper's E T⟨σ_A, σ_B⟩ = Φ⟨a, b⟩, p. 4)
--   - encoding: expectation over a uniformly random binding π: [n] → [n]; rounds 1, …, n; locations [n] → average over all n! elements of Equiv.Perm (Fin n) (avgPerm); rounds and locations are Fin n, Lean round i being round i + 1; reason: the same finite uniform distribution and the same game; no instance changes
-- source:
--   Bonamy, Pilipczuk, Sereni, On the effect of symmetry requirement for rendezvous on the complete graph, arXiv:2002.03764v1, p. 3 (PDF 4), Theorem 1; ε = 2⁻³⁶ on p. 12 (PDF 13), §3.6

import Mathlib
import Definitions.Def_RendezvousKn_Sym_Model

namespace RendezvousKn.Sym

theorem theorem_1 (n : ℕ) (hn : 2 ≤ n) (σ : Tactic n → ℝ)
    (hσ : σ ∈ stdSimplex ℝ (Tactic n)) :
    ((n : ℝ) + 1) / 2 + (2 : ℝ) ^ (-36 : ℤ) * n ≤ expWait σ σ := by sorry

end RendezvousKn.Sym
