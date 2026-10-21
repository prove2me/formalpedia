-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P27_finiteEntropyRegularity
-- name    : QAlgorithms.Papers.Independent.Next46.P27.finiteEntropyRegularity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T15:29:46.991975+00:00
-- url     : https://prove2.me/theorems/219eb265-b4e3-499f-a3c3-a36783e8b4cd
-- title:
--   Finite-cutoff entropy continuity and continuous first derivatives
-- statement:
--   For each integer $d\ge1$, consider the $d$-dimensional density matrices $X\in\mathbb C^{d\times d}$ with $X\succeq0$ and $\operatorname{tr}X=1$. Define entropy in nats by $S_d(X)=-\operatorname{Re}\operatorname{tr}(X\log X)$ using continuous spectral evaluation of $x\log x$ at zero. Then
--
--   $$S_d\text{ is continuous on all density matrices and is }C^1\text{ on the positive-definite relative interior}.$$
--
--   The interior is taken in the trace-one Hermitian affine space. This single statement applies at the $N$-dimensional input and $(N+1)$-dimensional output cutoff spaces. It does not assert continuity of infinite-dimensional entropy.
-- source:
--   The bosonic minimum output entropy conjecture and Lagrangian minimization, arXiv:0906.2758v3, PDF p. 5, Appendix 1: entropy regularity at finite cutoff

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P27

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P27

open Filter MeasureTheory

open scoped Topology ENNReal ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

-- Mathlib deliberately leaves the general C*-algebra calculus opt-in.

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

/-- PDF p.5, Appendix 1: nats entropy is continuous on each finite density
space and C1 on its relative positive-definite interior. ContDiffOn is a within-set
statement, so it does not differentiate the non-Hermitian cfc default.
Apply this same statement at dimensions N and N+1 for the two cutoff spaces. -/
theorem finiteEntropyRegularity (d : ℕ) (hd : 0 < d) :
    ContinuousOn QAlgorithms.Papers.Independent.Claimed50.P36.matrixEntropy (finiteDensities d) ∧
    ContDiffOn ℝ 1 QAlgorithms.Papers.Independent.Claimed50.P36.matrixEntropy
      (finiteInterior d) := by sorry

end QAlgorithms.Papers.Independent.Next46.P27

end
