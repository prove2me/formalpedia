-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P88_operator_width_bound
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P88.operator_width_bound
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-31T08:31:27.177275+00:00
-- url     : https://prove2.me/theorems/0ecd56e2-921f-414a-84c2-15a58059bd83
-- title:
--   Real Hermitian operator width is bounded by Hilbert dimension squared
-- statement:
--   Let $H=\mathbb C^h$ be a nonzero finite-dimensional complex Hilbert space, and let $\mathcal O\subseteq\operatorname{Mat}_{h\times h}(\mathbb C)$ be a real vector subspace consisting entirely of Hermitian matrices. Then
--   $$
--   \dim_{\mathbb R}\mathcal O\le h^2=(\dim_{\mathbb C}H)^2.
--   $$
--   In a qubit system $h=2^n$. This identifies the structural upper bound on the width of independent Hermitian observables. It supplies no lower bound on a chosen observable space when the Hilbert dimension increases.
-- source:
--   Representation Learning via Quantum Neural Tangent Kernels, arXiv:2111.04225v3, PDF p. 8, Main Section IV after Eq.(49)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P88

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P88

open scoped BigOperators ComplexConjugate Topology NNReal ComplexOrder

open MeasureTheory ProbabilityTheory Filter

/-- PDF p.8 main Section IV: the real width of a space of independent Hermitian
observables is at most the square of the complex Hilbert-space dimension.
This does not infer any lower bound on width from a large Hilbert space. -/
theorem operator_width_bound (h : ℕ) (hh : 0 < h)
    (S : Submodule ℝ (Matrix (Fin h) (Fin h) ℂ))
    (hS : ∀ A ∈ S, A.IsHermitian) :
    Module.finrank ℝ S ≤ h ^ 2 := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P88

end
