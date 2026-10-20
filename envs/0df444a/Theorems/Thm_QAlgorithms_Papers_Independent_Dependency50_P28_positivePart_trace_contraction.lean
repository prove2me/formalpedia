-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P28_positivePart_trace_contraction
-- name    : QAlgorithms.Papers.Independent.Dependency50.P28.positivePart_trace_contraction
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T17:46:44.863628+00:00
-- url     : https://prove2.me/theorems/7f7c895d-7ba3-4d51-957b-f5ca1898ed7c
-- title:
--   Positive trace-preserving maps contract the positive-part trace
-- statement:
--   Let A and B be arbitrary self-adjoint operators on a finite-dimensional complex Hilbert space, and let Φ be a positive, trace-preserving complex-linear map, with any finite output dimension. For every natural n and real a, the positive Jordan part satisfies
--
--   $$
--   \operatorname{Tr}(\Phi(A)-e^{na}\Phi(B))_+\leq\operatorname{Tr}(A-e^{na}B)_+.
--   $$
--
--   This comparison applies to arbitrary Hermitian inputs and is the positivity-based contraction used in the later testing bounds.
-- source:
--   Quantum hypothesis testing and the operational interpretation of the quantum Renyi relative entropies, arXiv:1309.3228v5, PDF p. 4, Lemma II.1

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P28

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P28

open scoped Matrix ComplexConjugate ComplexOrder BigOperators

open Filter QAlgorithms

open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)

open QAlgorithms.Papers.Independent.Information100.P07 (support positivePart positiveProjection)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- arXiv:1309.3228v5, PDF p.4: Positive trace-preserving maps contract the positive-part trace. The input matrices are arbitrary Hermitian operators: the subscript n does not impose a tensor-power hypothesis. The actual lemma starts on PDF p.4, following its derivation on p.3. No complete positivity is imposed. -/
theorem positivePart_trace_contraction (rho sigma : Mat I) (hrho : rho.IsHermitian) (hsigma : sigma.IsHermitian)
    (Phi : Mat I →ₗ[ℂ] Mat J) (hpos : Positive Phi) (htp : TP Phi) (n : ℕ) (a : ℝ) :
    tr (positivePart (Phi rho - (Real.exp ((n : ℝ) * a) : ℂ) • Phi sigma)) ≤
      tr (positivePart (rho - (Real.exp ((n : ℝ) * a) : ℂ) • sigma)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P28

end
