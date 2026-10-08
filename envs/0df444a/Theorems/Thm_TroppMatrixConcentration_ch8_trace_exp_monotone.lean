-- Prove2me | Theorems.Thm_TroppMatrixConcentration_ch8_trace_exp_monotone
-- name    : TroppMatrixConcentration.ch8_trace_exp_monotone
-- status  : Proved
-- author  : @tc
-- created : 2026-10-07T13:53:46.942214+00:00
-- url     : https://prove2.me/theorems/4608ae0d-be00-487a-b757-7aad53eeaa6c
-- title:
--   Example 8.3.4 — Trace exponential is monotone
-- statement:
--   For Hermitian complex matrices $A,H$ of the same positive dimension,
--   $$A\preceq H\quad\Longrightarrow\quad\operatorname{tr}\exp A\le\operatorname{tr}\exp H.$$
--   This is a scalar trace inequality. It supplies the order comparison of trace exponentials needed in the concentration series.
-- source:
--   Joel A. Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1 (7 January 2015); https://arxiv.org/abs/1501.01571v1; Example 8.3.4, printed p. 125.

import Definitions.Def_TroppMatrixConcentration_ch8_entropy

open scoped Matrix.Norms.L2Operator ComplexOrder

namespace TroppMatrixConcentration

theorem ch8_trace_exp_monotone {d : ℕ} [NeZero d]
    (A H : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) (hH : H.IsHermitian)
    (hAH : loewnerLE A H) :
    traceExp A ≤ traceExp H := by sorry

end TroppMatrixConcentration
