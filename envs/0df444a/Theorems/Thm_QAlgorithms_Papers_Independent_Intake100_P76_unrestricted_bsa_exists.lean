-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P76_unrestricted_bsa_exists
-- name    : QAlgorithms.Papers.Independent.Intake100.P76.unrestricted_bsa_exists
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T18:20:22.693169+00:00
-- url     : https://prove2.me/theorems/f1bf5b39-8054-40a6-bb7b-76dd0de91384
-- title:
--   Unrestricted best separable approximation exists
-- statement:
--   Let $H_A$ and $H_B$ be finite-dimensional nonzero complex Hilbert spaces, with $H_A$ the first tensor factor, and let $\rho$ be a positive semidefinite operator of trace one on $H_A\otimes H_B$. An unnormalized separable positive operator means a finite nonnegative sum of tensor products of local density matrices; zero is allowed. There exists such an operator $S$ satisfying
--
--   $$\rho-S\succeq0,\qquad 0\leq\operatorname{Tr}S\leq1,\qquad \operatorname{Tr}T\leq\operatorname{Tr}S\quad\text{for every separable }T\succeq0\text{ with }\rho-T\succeq0.$$
--
--   This is an attained unrestricted optimum. It supplies the mathematical decomposition independently of any numerical procedure.
-- source:
--   Separability and entanglement of composite quantum systems, arXiv:quant-ph/9707043v1, PDF p. 2, Abstract and pp.2-3, unnumbered: unrestricted best separable approximation exists

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P76

noncomputable section

open scoped Matrix ComplexOrder ComplexConjugate

open QAlgorithms QAlgorithms.Entanglement

namespace QAlgorithms.Papers.Independent.Intake100.P76

variable {A B I : Type*} [Fintype A] [Fintype B] [Fintype I]
  [DecidableEq A] [DecidableEq B] [DecidableEq I]

/-- PDF p.2, opening paragraph, and p.3 after Theorem 2: unrestricted BSA
existence in every finite, nonempty bipartite dimension. -/
theorem unrestricted_bsa_exists [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (hrho : IsDensityMatrix rho) :
    ∃ S, IsBSA rho S ∧ 0 ≤ S.trace.re ∧ S.trace.re ≤ 1 := by sorry

end QAlgorithms.Papers.Independent.Intake100.P76

end
