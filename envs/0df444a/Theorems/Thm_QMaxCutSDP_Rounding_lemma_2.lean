-- Prove2me | Theorems.Thm_QMaxCutSDP_Rounding_lemma_2
-- name    : QMaxCutSDP.Rounding.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:48:15.445983+00:00
-- url     : https://prove2.me/theorems/660c48bf-62c0-4536-965f-a4057476025b
-- title:
--   Lemma 2 — SDP (S) relaxes level-two Lasserre
-- statement:
--   Given any feasible matrix $M$ for the level-two canonical Lasserre program on a weighted graph $G$, there are a dimension $N$ and vectors $v_0,v_{i,a},v_{ij,a}\in\mathbb R^N$ satisfying the constraints of SDP (S) such that
--   $$L_2(G;M)\le S(G;v).$$
--   This transfers the quantum-state relaxation to the vector program used by the rounding algorithm.
-- source:
--   Lee, Optimizing quantum circuit parameters via SDP, arXiv:2209.00789v1, p. 6, Lemma 2

import Mathlib
import Definitions.Def_QMaxCutSDP_Rounding_Model

open Matrix MeasureTheory

namespace QMaxCutSDP.Rounding

/-- Lee, Lemma 2, p. 6. The vector program (S) relaxes level two. -/
theorem lemma_2 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Fin n → Fin n → ℝ) (M : Matrix (PIndex n 2) (PIndex n 2) ℝ)
    (hM : IsLasserreFeasible n 2 M) :
    ∃ (N : ℕ) (v : SDPVec n N),
      IsSFeasible v ∧ lasserreObj G w (by decide) M ≤ sObj G w v := by sorry
end QMaxCutSDP.Rounding
