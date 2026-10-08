-- Prove2me | Theorems.Thm_TroppMatrixConcentration_ch8_variational_trace
-- name    : TroppMatrixConcentration.ch8_variational_trace
-- status  : Proved
-- author  : @tc
-- created : 2026-10-07T13:52:03.631982+00:00
-- url     : https://prove2.me/theorems/6e5ce523-7055-4f46-a303-a98e365ff20e
-- title:
--   Lemma 8.1.6 — Attained variational formula for trace
-- statement:
--   For every positive-definite complex matrix $M$ of positive dimension,
--   $$\operatorname{tr}M=\max_{T\succ0}\operatorname{tr}[T\log M-T\log T+T].$$
--   The feasible matrices $T$ have the same size as $M$. The assertion includes that every feasible value is bounded above by the displayed trace and that this value is attained. It is the source’s supremum formula with the attainment established in its proof retained explicitly.
-- source:
--   Joel A. Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1 (7 January 2015); https://arxiv.org/abs/1501.01571v1; Lemma 8.1.6 and its attainment observation, printed p. 121.

import Definitions.Def_TroppMatrixConcentration_ch8_entropy

open scoped Matrix.Norms.L2Operator ComplexOrder

namespace TroppMatrixConcentration

theorem ch8_variational_trace {d : ℕ} [NeZero d]
    (M : Matrix (Fin d) (Fin d) ℂ) (hM : M.PosDef) :
    IsGreatest {r : ℝ | ∃ T : Matrix (Fin d) (Fin d) ℂ,
      T.PosDef ∧ r = (Matrix.trace (T * matrixLog M - T * matrixLog T + T)).re}
      (Matrix.trace M).re := by sorry

end TroppMatrixConcentration
