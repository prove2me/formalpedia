-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P17_exists_jordan_decomposition
-- name    : QAlgorithms.Papers.Independent.Support50.P17.exists_jordan_decomposition
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-29T18:22:02.435564+00:00
-- url     : https://prove2.me/theorems/ad573038-9636-46e4-93de-327dcd788889
-- title:
--   Jordan decomposition of the difference of two density matrices
-- statement:
--   Let $\rho,\sigma$ be density matrices (positive semidefinite, trace one) on a finite-dimensional complex Hilbert space and let $T=\tfrac12\|\rho-\sigma\|_1$ be their trace distance. Then there are positive semidefinite operators $X_+,X_-$ such that
--
--   1. $\rho-\sigma=X_+-X_-$;
--   2. $\operatorname{Tr}X_+=\operatorname{Tr}X_-=T$;
--   3. $X_++X_-\le T\,I$.
--
--   Here $X_\pm$ are the positive and negative parts of the Hermitian operator $\rho-\sigma$; the last item holds because $X_+$ and $X_-$ have orthogonal supports and each has operator norm at most its trace $T$. This decomposition is the standard first step in continuity estimates phrased via trace distance.
--
--   **Formalization Note** $T$ is the frozen `traceDistance` $=\tfrac12\operatorname{Tr}\sqrt{(\rho-\sigma)^*(\rho-\sigma)}$; traces are complex numbers and $T$ is cast to $\mathbb C$.
-- source:
--   Nielsen--Chuang, Quantum Computation and Quantum Information, Section 9.2.1, proof of Eq. (9.22); used in Audenaert--Eisert, Continuity bounds on the quantum relative entropy - II, arXiv:1105.2656v3, proof of Corollary 1 (PDF p. 9), Delta = T(P - Q)

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P17

noncomputable section

open MeasureTheory

open scoped Matrix ComplexOrder Matrix.Norms.L2Operator

open QAlgorithms.Papers.Independent.Dependency50.P21 (IsSupported relativeEntropy)

namespace QAlgorithms.Papers.Independent.Support50.P17

attribute [local instance] Classical.propDecidable Classical.decEq

theorem exists_jordan_decomposition {I : Type*} [Fintype I] [DecidableEq I]
    (rho sigma : Matrix I I ℂ) (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma) :
    ∃ Xp Xm : Matrix I I ℂ, Xp.PosSemidef ∧ Xm.PosSemidef ∧ rho - sigma = Xp - Xm ∧
      Xp.trace = ((traceDistance rho sigma : ℝ) : ℂ) ∧
      Xm.trace = ((traceDistance rho sigma : ℝ) : ℂ) ∧
      (((traceDistance rho sigma : ℝ) : ℂ) • (1 : Matrix I I ℂ) - (Xp + Xm)).PosSemidef := by sorry

end QAlgorithms.Papers.Independent.Support50.P17

end
