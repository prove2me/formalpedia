-- Prove2me | Theorems.Thm_TroppMatrixConcentration_ch8_variational_trace_exp
-- name    : TroppMatrixConcentration.ch8_variational_trace_exp
-- status  : Proved
-- author  : @tc
-- created : 2026-10-07T13:52:21.535976+00:00
-- url     : https://prove2.me/theorems/77009dcc-fd98-4390-b1e4-d99e3af6a4ab
-- title:
--   Equation 8.1.2 — Variational trace exponential
-- statement:
--   For every Hermitian complex matrix $H$ and positive-definite complex matrix $A$ of the same positive dimension,
--   $$\operatorname{tr}\exp(H+\log A)=\max_{T\succ0}\{\operatorname{tr}(TH)+\operatorname{tr}A-D(T;A)\}.$$
--   The maximum is over positive-definite matrices of the same size and is asserted to be attained. This gives the exact variational objective used in the source’s Lieb concavity argument.
-- source:
--   Joel A. Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1 (7 January 2015); https://arxiv.org/abs/1501.01571v1; Equation (8.1.2), together with the attainment in Lemma 8.1.6, printed p. 121.

import Definitions.Def_TroppMatrixConcentration_ch8_entropy

open scoped Matrix.Norms.L2Operator ComplexOrder

namespace TroppMatrixConcentration

theorem ch8_variational_trace_exp {d : ℕ} [NeZero d]
    (H A : Matrix (Fin d) (Fin d) ℂ) (hH : H.IsHermitian) (hA : A.PosDef) :
    IsGreatest {r : ℝ | ∃ T : Matrix (Fin d) (Fin d) ℂ,
      T.PosDef ∧ r = (Matrix.trace (T * H)).re + (Matrix.trace A).re -
        ch8_relativeEntropy T A}
      (traceExp (H + matrixLog A)) := by sorry

end TroppMatrixConcentration
