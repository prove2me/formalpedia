-- Prove2me | Theorems.Thm_QMaxCutSDP_Rounding_lemma_1
-- name    : QMaxCutSDP.Rounding.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:48:06.498354+00:00
-- url     : https://prove2.me/theorems/b758a731-06b4-4f96-932a-03ab7bc815d0
-- title:
--   Lemma 1 — level-k Lasserre relaxes Quantum Max Cut
-- statement:
--   Let $G$ be a weighted graph on $n$ vertices with nonnegative edge weights, and let $2\le k\le n$. For every unit $n$-qubit state $|\phi\rangle$, there is a feasible level-$k$ canonical Lasserre matrix $M$ such that
--   $$\langle\phi|H|\phi\rangle\le L_k(G;M).$$
--   Thus the level-$k$ optimum upper-bounds the energy of every quantum state.
--
--   **Formalization Note** The lower bound $k\ge2$ is necessary because the displayed objective indexes two-qubit Pauli strings, absent from $P_n(1)$.
-- source:
--   Lee, Optimizing quantum circuit parameters via SDP, arXiv:2209.00789v1, p. 4, Lemma 1; proof p. 14

import Mathlib
import Definitions.Def_QMaxCutSDP_Rounding_Model

open Matrix MeasureTheory

namespace QMaxCutSDP.Rounding

/-- Lee, Lemma 1, p. 4. The level-k Lasserre program relaxes Quantum Max Cut. -/
theorem lemma_1 {n k : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Fin n → Fin n → ℝ) (hw : ∀ i j, 0 ≤ w i j)
    (φ : State n) (hφ : star φ ⬝ᵥ φ = 1) :
    ∃ M : Matrix (PIndex n k) (PIndex n k) ℝ,
      IsLasserreFeasible n k M ∧ energy G w φ ≤ lasserreObj G w hk M := by sorry
end QMaxCutSDP.Rounding
