-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P28_psiJoint
-- name    : QAlgorithms.Papers.Independent.Intake100.P28.psiJoint
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:36:04.770001+00:00
-- url     : https://prove2.me/theorems/7dd97b07-e73b-432a-afef-0f389180aec5
-- title:
--   Lemma 3.2: convexity and concavity of Psi
-- statement:
--   Let $n,m$ be positive integers. All matrices are complex and positive semidefinite unless otherwise specified, including singular matrices and zero. For $p,q>0$, put
--   $$
--   \Phi_{p,q}(A_1,\ldots,A_m)=\left(\operatorname{Tr}(\sum_j A_j^p)^{q/p}\right)^{1/q},\quad
--   \Psi_{p,q}(A)=\left(\operatorname{Tr}(\operatorname{Tr}_2 A^p)^{q/p}\right)^{1/q},\quad
--   \Upsilon_{p,q}^{B}(A)=\operatorname{Tr}(B^*A^pB)^{q/p}.
--   $$
--   Here powers are spectral powers, $B$ is an arbitrary fixed complex matrix, and $\operatorname{Tr}_2$ is the unnormalized partial trace over the second factor of $\mathbb C^m\otimes\mathbb C^n$. Convexity and concavity use every mixture weight in $[0,1]$.
--
--   For every pair of positive tensor-factor dimensions,
--   $$
--   1\le p\le2,\ q\ge1\ \Longrightarrow\ \Psi_{p,q}\text{ is convex},\qquad
--   0<p\le q\le1\ \Longrightarrow\ \Psi_{p,q}\text{ is concave}.
--   $$
--   Both assertions hold on the full positive semidefinite cone. The partial trace is unnormalized.
--
--   This provides the convexity needed for the decomposition norm and the three-factor inequality.
-- source:
--   A Minkowski Type Trace Inequality and Strong Subadditivity of Quantum Entropy II: Convexity and Concavity, arXiv:0710.4167v3, PDF p. 11, Lemma 3.2

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P28

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Dependency50.P35
  (spectralPower tr leftMarginal rightMarginal marginalAC)

namespace QAlgorithms.Papers.Independent.Intake100.P28

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Lemma 3.2, PDF pp.11–12; all positive factor sizes, unnormalized trace. -/
theorem psiJoint (p q : ℝ) :
    (1 ≤ p → p ≤ 2 → 1 ≤ q → PsiConvex p q) ∧
    (0 < p → p ≤ q → q ≤ 1 → PsiConcave p q) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P28

end
