-- Prove2me | Theorems.Thm_QMCTriFree_Circuit_lemma_7
-- name    : QMCTriFree.Circuit.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:30:01.683155+00:00
-- url     : https://prove2.me/theorems/6606d795-5ec6-4e68-8deb-deda984007d4
-- title:
--   Lemma 7 — monogamy in $\mathrm{Lasserre}_2$: $\sum_{j\in S}x_{ij}\le1$ over any set of neighbours of $i$
-- statement:
--   Let $M$ be feasible for $\mathrm{Lasserre}_2(H)$ and let $x_{ij}$ be its edge values. For every vertex $i$ and every set $S$ of neighbours of $i$,
--   $$\sum_{j\in S}x_{ij}\le 1 .$$
--
--   The relaxation "knows about" monogamy of entanglement: the edges of a star cannot all be close to the singlet. This bound, through Corollary 8, controls how much the rotations of neighbouring edges cost.
--
--   **Formalization Note** Only the $x$-part is stated (the $y$-part concerns the EPR Hamiltonian). Neighbours of $i$ are vertices $k\ne i$ with $w_{ik}\ne0$; no other property of $w$ is assumed.
-- source:
--   King, An Improved Approximation Algorithm for Quantum Max-Cut on Triangle-Free Graphs, arXiv:2209.02589v3, p. 7, Lemma 7

import Mathlib
import Definitions.Def_QMCTriFree_Circuit_Lasserre

set_option autoImplicit false

open QMCProduct.HalfApprox Matrix MeasureTheory ProbabilityTheory

namespace QMCTriFree.Circuit

/-- King, arXiv:2209.02589v3, p. 7, Lemma 7 (the `x` part): for every feasible `M` of
`Lasserre_2(H)`, every vertex `i` and every set `S` of neighbours of `i`, `∑_{j∈S} x_ij ≤ 1`. -/
theorem lemma_7 {n : ℕ} (w : Fin n → Fin n → ℝ) (M : Matrix (P2 n) (P2 n) ℝ)
    (hM : IsFeasible M) (i : Fin n) (S : Finset (Fin n)) (hS : S ⊆ nbrs w i) :
    ∑ j ∈ S, xval M i j ≤ 1 := by sorry

end QMCTriFree.Circuit
