-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P28_phiJoint
-- name    : QAlgorithms.Papers.Independent.Intake100.P28.phiJoint
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:35:26.043718+00:00
-- url     : https://prove2.me/theorems/622eb9c7-9786-49d7-8854-c4f41430bfb4
-- title:
--   Lemma 3.1: joint convexity and concavity of Phi
-- statement:
--   Let $n,m$ be positive integers. All matrices are complex and positive semidefinite unless otherwise specified, including singular matrices and zero. For $p,q>0$, put
--   $$
--   \Phi_{p,q}(A_1,\ldots,A_m)=\left(\operatorname{Tr}(\sum_j A_j^p)^{q/p}\right)^{1/q},\quad
--   \Psi_{p,q}(A)=\left(\operatorname{Tr}(\operatorname{Tr}_2 A^p)^{q/p}\right)^{1/q},\quad
--   \Upsilon_{p,q}^{B}(A)=\operatorname{Tr}(B^*A^pB)^{q/p}.
--   $$
--   Here powers are spectral powers, $B$ is an arbitrary fixed complex matrix, and $\operatorname{Tr}_2$ is the unnormalized partial trace over the second factor of $\mathbb C^m\otimes\mathbb C^n$. Convexity and concavity use every mixture weight in $[0,1]$.
--
--   For every positive tuple length and positive matrix dimension,
--   $$
--   1\le p\le2,\ q\ge1\ \Longrightarrow\ \Phi_{p,q}\text{ is jointly convex},\qquad
--   0<p\le q\le1\ \Longrightarrow\ \Phi_{p,q}\text{ is jointly concave}.
--   $$
--   Each component may be singular or zero, and the mixture uses one common weight for all tuple entries.
--
--   This transfers the Upsilon results to the rooted tuple functional.
-- source:
--   A Minkowski Type Trace Inequality and Strong Subadditivity of Quantum Entropy II: Convexity and Concavity, arXiv:0710.4167v3, PDF p. 10, Lemma 3.1

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P28

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Dependency50.P35
  (spectralPower tr leftMarginal rightMarginal marginalAC)

namespace QAlgorithms.Papers.Independent.Intake100.P28

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Lemma 3.1, PDF pp.10–11; all positive tuple lengths, including zero entries. -/
theorem phiJoint (p q : ℝ) :
    (1 ≤ p → p ≤ 2 → 1 ≤ q → PhiConvex p q) ∧
    (0 < p → p ≤ q → q ≤ 1 → PhiConcave p q) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P28

end
