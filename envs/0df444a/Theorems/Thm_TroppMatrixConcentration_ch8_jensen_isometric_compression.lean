-- Prove2me | Theorems.Thm_TroppMatrixConcentration_ch8_jensen_isometric_compression
-- name    : TroppMatrixConcentration.ch8_jensen_isometric_compression
-- status  : Proved
-- author  : @tc
-- created : 2026-10-07T14:47:18.697978+00:00
-- url     : https://prove2.me/theorems/398be89f-aaba-4d40-825d-08d63c7b2f89
-- title:
--   Operator convexity under isometric compression
-- statement:
--   Let $f$ be operator convex on a real interval $I$, let $A$ be a finite-dimensional Hermitian complex matrix with spectrum in $I$, and let $K$ be a rectangular isometry, $K^*K=I$. Then $$f(K^*AK)\preceq K^*f(A)K.$$ This compression form yields the two-term operator Jensen inequality.
-- source:
--   Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1, Theorem 8.5.2 and its unitary dilation proof, printed pp. 132–133.

import Definitions.Def_TroppMatrixConcentration_ch8_entropy

open scoped Matrix.Norms.L2Operator ComplexOrder

namespace TroppMatrixConcentration

theorem ch8_jensen_isometric_compression
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (I : Set ℝ) (f : ℝ → ℝ) (hf : ch8_operatorConvexOn I f)
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (hAI : spectrum ℝ A ⊆ I)
    (K : Matrix ι κ ℂ) (hK : K.conjTranspose * K = 1) :
    loewnerLE (ch8_matrixFunction f (K.conjTranspose * A * K))
      (K.conjTranspose * ch8_matrixFunction f A * K) := by sorry

end TroppMatrixConcentration
