-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P76_bsa_trace_monotone_and_unique
-- name    : QAlgorithms.Papers.Independent.Intake100.P76.bsa_trace_monotone_and_unique
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T18:24:39.73132+00:00
-- url     : https://prove2.me/theorems/ec20e914-b9fb-4bab-911f-a8f8770bd6f6
-- title:
--   Monotonicity and uniqueness of the optimal trace
-- statement:
--   Let $H_A$ and $H_B$ be finite-dimensional nonzero complex Hilbert spaces, with $H_A$ the first tensor factor, and let $\rho$ be a positive semidefinite operator of trace one on $H_A\otimes H_B$. Let $V,W$ be sets of unit product vectors in $\operatorname{range}\rho$. A restricted optimizer over a set maximizes the trace among its finite nonnegative projector sums that can be subtracted while leaving a positive semidefinite residual. For any actual restricted optimizers, the following hold:
--
--   $$V\subseteq W,\ S\in\mathrm{BSA}_V(\rho),\ T\in\mathrm{BSA}_W(\rho)\ \Longrightarrow\ \operatorname{Tr}S\leq\operatorname{Tr}T,$$
--
--   $$S,T\in\mathrm{BSA}_V(\rho)\ \Longrightarrow\ \operatorname{Tr}S=\operatorname{Tr}T.$$
--
--   Thus enlarging the allowed set cannot worsen an attained optimum, and the optimal scalar trace is unique even when its optimizing matrix is not.
-- source:
--   Separability and entanglement of composite quantum systems, arXiv:quant-ph/9707043v1, PDF p. 2, Unnumbered after Theorem 1: monotonicity and uniqueness of the optimal trace

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P76

noncomputable section

open scoped Matrix ComplexOrder ComplexConjugate

open QAlgorithms QAlgorithms.Entanglement

namespace QAlgorithms.Papers.Independent.Intake100.P76

variable {A B I : Type*} [Fintype A] [Fintype B] [Fintype I]
  [DecidableEq A] [DecidableEq B] [DecidableEq I]

/-- PDF p.2, paragraph after Theorem 1: monotonicity under enlarging V and
uniqueness of the optimal trace (not necessarily the optimizer matrix).
Both assertions quantify over actual attained optimizers. -/
theorem bsa_trace_monotone_and_unique [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (hrho : IsDensityMatrix rho)
    (V W : Set (EuclideanSpace ℂ (A × B)))
    (hV : ∀ v ∈ V, IsUnitProduct v ∧ v ∈ LinearMap.range (Matrix.toEuclideanLin rho))
    (hW : ∀ v ∈ W, IsUnitProduct v ∧ v ∈ LinearMap.range (Matrix.toEuclideanLin rho)) :
    (∀ S T, V ⊆ W → IsBSAOver rho V S → IsBSAOver rho W T →
      S.trace.re ≤ T.trace.re) ∧
    (∀ S T, IsBSAOver rho V S → IsBSAOver rho V T → S.trace.re = T.trace.re) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P76

end
