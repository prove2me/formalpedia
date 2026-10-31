-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P28_allOperatorsNorm
-- name    : QAlgorithms.Papers.Independent.Intake100.P28.allOperatorsNorm
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:29:33.291192+00:00
-- url     : https://prove2.me/theorems/ba32d4f4-cdb4-438e-a7d5-c82686fc0771
-- title:
--   Unnumbered main result: norm on all operators via off-diagonal dilation
-- statement:
--   Let $n,m$ be positive integers. All matrices are complex and positive semidefinite unless otherwise specified, including singular matrices and zero. For $p,q>0$, put
--   $$
--   \Phi_{p,q}(A_1,\ldots,A_m)=\left(\operatorname{Tr}(\sum_j A_j^p)^{q/p}\right)^{1/q},\quad
--   \Psi_{p,q}(A)=\left(\operatorname{Tr}(\operatorname{Tr}_2 A^p)^{q/p}\right)^{1/q},\quad
--   \Upsilon_{p,q}^{B}(A)=\operatorname{Tr}(B^*A^pB)^{q/p}.
--   $$
--   Here powers are spectral powers, $B$ is an arbitrary fixed complex matrix, and $\operatorname{Tr}_2$ is the unnormalized partial trace over the second factor of $\mathbb C^m\otimes\mathbb C^n$. Convexity and concavity use every mixture weight in $[0,1]$.
--
--   Fix $1\le p\le2$, $q\ge1$, and nonzero finite factors $H_1,H_2$. Let $N$ denote the preceding decomposition infimum, evaluated using the factorization $H_1\otimes(H_2\otimes\mathbb C^2)$. For every complex operator $X$ on $H_1\otimes H_2$, set
--   $$
--   \widehat X=\begin{pmatrix}0&X\\X^*&0\end{pmatrix},\qquad M_{p,q}(X)=\tfrac12N_{p,q}(\widehat X).
--   $$
--   Then $M$ is a complex norm: it is nonnegative, vanishes exactly at zero, and for all complex scalars $z$ and all $X,Y$,
--   $$
--   M(zX)=|z|M(X),\qquad M(X+Y)\le M(X)+M(Y).
--   $$
--   The two-dimensional ancilla belongs to the traced second factor. The coefficient $1/2$ is exactly the printed one.
--
--   This gives the paper's first norm construction for arbitrary operators; no agreement with the self-adjoint norm is asserted.
-- source:
--   A Minkowski Type Trace Inequality and Strong Subadditivity of Quantum Entropy II: Convexity and Concavity, arXiv:0710.4167v3, PDF p. 6, Unnumbered main result

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P28

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Dependency50.P35
  (spectralPower tr leftMarginal rightMarginal marginalAC)

namespace QAlgorithms.Papers.Independent.Intake100.P28

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Equation (1.14), PDF pp.6–7: a complex norm; C^2 is in the traced factor. -/
theorem allOperatorsNorm {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (p q : ℝ) (hp : 1 ≤ p) (hp2 : p ≤ 2) (hq : 1 ≤ q) :
    IsMatrixNorm (fullGauge (I := Fin m) (J := Fin n) p q) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P28

end
