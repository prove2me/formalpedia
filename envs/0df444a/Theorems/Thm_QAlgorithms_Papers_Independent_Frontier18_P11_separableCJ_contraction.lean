-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P11_separableCJ_contraction
-- name    : QAlgorithms.Papers.Independent.Frontier18.P11.separableCJ_contraction
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:33:34.781461+00:00
-- url     : https://prove2.me/theorems/9709b81f-6f9e-4ab3-ba71-f810e0f913c5
-- title:
--   Lemma 2: separable normalized CJ operators are contractions
-- statement:
--   Let $H_A,H_B$ be complex separable Hilbert spaces, and let $\Omega$ be a bounded positive operator on the completed Hilbert tensor product $H_B\otimes H_A$. Suppose $\operatorname{Tr}_B\Omega=I_A$ in the full matrix-element sense. Let $C_{BA}$ consist of the operators with this normalization that lie in the weak operator closure of finite sums $\sum_{\alpha=1}^n\rho_\alpha\otimes M_\alpha$, where every $\rho_\alpha$ is a positive trace-class operator of trace one on $H_B$, and the positive bounded operators $M_\alpha$ on $H_A$ satisfy $\sum_\alpha M_\alpha=I_A$. If $\Omega\in C_{BA}$, then
--
--   $$
--   \|\Omega\|\le 1.
--   $$
--
--   This controls the norm of separable CJ operators in infinite dimension. It does not identify $C_{BA}$ with the trace-norm closed set of bipartite density operators.
--
--   **Formalization Note** Positive bounded output operators are required to have a convergent diagonal trace series of sum one in a countable orthonormal Hilbert basis; for positive operators this is exactly the density-operator condition.
-- source:
--   On the Choi-Jamiolkowski Correspondence in Infinite Dimensions, arXiv:1004.0196v3, PDF p. 6, Lemma 2: separable CJ operators are contractions

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P11

noncomputable section

open scoped TensorProduct ComplexOrder

namespace QAlgorithms.Papers.Independent.Frontier18.P11

section Operators

variable {A B : Type*}

variable [NormedAddCommGroup A] [InnerProductSpace ℂ A]

variable [NormedAddCommGroup B] [InnerProductSpace ℂ B]

/-- Lemma 2, PDF p.6: every separable normalized bounded CJ operator is a
contraction. All spaces are complex separable Hilbert spaces; e is an arbitrary
countable orthonormal Hilbert basis in the output space. -/
theorem separableCJ_contraction
    [CompleteSpace A] [CompleteSpace B]
    [SecondCountableTopology A] [SecondCountableTopology B]
    {I : Type*} [Countable I] (e : HilbertBasis I ℂ B)
    (O : JointHilbert A B →L[ℂ] JointHilbert A B) (hO : separableCJ e O) :
    ‖O‖ ≤ 1 := by sorry

end Operators

end QAlgorithms.Papers.Independent.Frontier18.P11

end
