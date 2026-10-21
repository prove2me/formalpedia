-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P38_contractiveTrace
-- name    : QAlgorithms.Papers.Independent.Renew46.P38.contractiveTrace
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T21:08:36.271083+00:00
-- url     : https://prove2.me/theorems/75efd3a3-1a8d-4d22-8f76-5a228bf14dfb
-- title:
--   Contractive matrix trace Jensen inequality
-- statement:
--   Let $I$ be a real interval containing $0$. Let $f:I\to\mathbb R$ be continuous and convex, with $f(0)\leq0$. For all positive integers $m,n$, all self-adjoint complex $m\times m$ matrices $x_i$ with spectra in $I$, and all complex $m\times m$ matrices $a_i$ satisfying $\sum_i a_i^*a_i\leq1$,
--   $$\operatorname{Tr}\!\left(f\!\left(\sum_i a_i^*x_i a_i\right)\right)\leq\operatorname{Tr}\!\left(\sum_i a_i^*f(x_i)a_i\right).$$
--   The trace is the ordinary unnormalized trace, represented by its real part. Taking $n=1$ gives display (8) of Remark 2.6. This is a forward implication; it does not assert a one-term converse.
-- source:
--   Jensen's Operator Inequality, arXiv:math/0204049v1, PDF p. 4, Corollary 2.5 (Contractive Version)

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P38

noncomputable section

open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal

namespace QAlgorithms.Papers.Independent.Renew46.P38

universe u

/-- Hansen--Pedersen, Corollary 2.5, PDF p. 4.
Its n=1 specialization is display (8) in Remark 2.6; no converse is asserted. -/
theorem contractiveTrace (I : Set ℝ) (f : ℝ → ℝ)
    (hI : Set.OrdConnected I) (hf : ContinuousOn f I) (hconv : ConvexOn ℝ I f)
    (hzero : 0 ∈ I) (hfzero : f 0 ≤ 0) :
    ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → MatrixTraceJensen I f m n true := by sorry

end QAlgorithms.Papers.Independent.Renew46.P38

end
