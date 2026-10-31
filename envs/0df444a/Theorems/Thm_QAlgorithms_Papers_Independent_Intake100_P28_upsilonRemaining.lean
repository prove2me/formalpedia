-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P28_upsilonRemaining
-- name    : QAlgorithms.Papers.Independent.Intake100.P28.upsilonRemaining
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:34:23.143282+00:00
-- url     : https://prove2.me/theorems/d946a40e-980b-483a-9552-c994e1d6ea05
-- title:
--   Lemma 2.7: remaining convexity and concavity of Upsilon
-- statement:
--   Let $n,m$ be positive integers. All matrices are complex and positive semidefinite unless otherwise specified, including singular matrices and zero. For $p,q>0$, put
--   $$
--   \Phi_{p,q}(A_1,\ldots,A_m)=\left(\operatorname{Tr}(\sum_j A_j^p)^{q/p}\right)^{1/q},\quad
--   \Psi_{p,q}(A)=\left(\operatorname{Tr}(\operatorname{Tr}_2 A^p)^{q/p}\right)^{1/q},\quad
--   \Upsilon_{p,q}^{B}(A)=\operatorname{Tr}(B^*A^pB)^{q/p}.
--   $$
--   Here powers are spectral powers, $B$ is an arbitrary fixed complex matrix, and $\operatorname{Tr}_2$ is the unnormalized partial trace over the second factor of $\mathbb C^m\otimes\mathbb C^n$. Convexity and concavity use every mixture weight in $[0,1]$.
--
--   The remaining parameter ranges satisfy
--   $$
--   1\le q\le p\le2\ \Longrightarrow\ \Upsilon_{p,q}^{B}\text{ is convex},\qquad
--   0<p\le q\le1\ \Longrightarrow\ \Upsilon_{p,q}^{B}\text{ is concave}.
--   $$
--   Both properties hold on the full positive semidefinite cone for every positive matrix dimension and every fixed complex $B$. The equality case $p=q$ is included.
--
--   Together with Lemma 2.1 this supplies the full positive-parameter Upsilon conclusions of Theorem 1.1.
-- source:
--   A Minkowski Type Trace Inequality and Strong Subadditivity of Quantum Entropy II: Convexity and Concavity, arXiv:0710.4167v3, PDF p. 10, Lemma 2.7

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P28

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Dependency50.P35
  (spectralPower tr leftMarginal rightMarginal marginalAC)

namespace QAlgorithms.Papers.Independent.Intake100.P28

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Lemma 2.7, PDF p.10; positive p convention from its proof on p.13. -/
theorem upsilonRemaining (p q : ℝ) :
    (1 ≤ q → q ≤ p → p ≤ 2 → UConvex p q) ∧
    (0 < p → p ≤ q → q ≤ 1 → UConcave p q) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P28

end
