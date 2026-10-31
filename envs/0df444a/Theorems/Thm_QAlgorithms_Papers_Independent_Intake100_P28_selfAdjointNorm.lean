-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P28_selfAdjointNorm
-- name    : QAlgorithms.Papers.Independent.Intake100.P28.selfAdjointNorm
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:28:38.960441+00:00
-- url     : https://prove2.me/theorems/9301d531-093f-4624-a34c-d0cfb8f205d0
-- title:
--   Unnumbered main result: self-adjoint Lq(Lp) norm
-- statement:
--   Let $n,m$ be positive integers. All matrices are complex and positive semidefinite unless otherwise specified, including singular matrices and zero. For $p,q>0$, put
--   $$
--   \Phi_{p,q}(A_1,\ldots,A_m)=\left(\operatorname{Tr}(\sum_j A_j^p)^{q/p}\right)^{1/q},\quad
--   \Psi_{p,q}(A)=\left(\operatorname{Tr}(\operatorname{Tr}_2 A^p)^{q/p}\right)^{1/q},\quad
--   \Upsilon_{p,q}^{B}(A)=\operatorname{Tr}(B^*A^pB)^{q/p}.
--   $$
--   Here powers are spectral powers, $B$ is an arbitrary fixed complex matrix, and $\operatorname{Tr}_2$ is the unnormalized partial trace over the second factor of $\mathbb C^m\otimes\mathbb C^n$. Convexity and concavity use every mixture weight in $[0,1]$.
--
--   Fix $1\le p\le2$, $q\ge1$, and finite nonzero tensor factors. For every Hermitian $X$, define
--   $$
--   N_{p,q}(X)=\inf_{X=A-B,\ A,B\ge0}\bigl(\Psi_{p,q}(A)+\Psi_{p,q}(B)\bigr).
--   $$
--   This defines a real norm on the Hermitian real vector space: $N(X)\ge0$, $N(X)=0$ if and only if $X=0$, and for every real $t$ and Hermitian $X,Y$,
--   $$
--   N(tX)=|t|N(X),\qquad N(X+Y)\le N(X)+N(Y).
--   $$
--   The feasible set is nonempty by the spectral positive and negative parts of $X$; the objective is nonnegative. No minimizing decomposition is asserted.
--
--   This extends the positive-cone functional to a norm on self-adjoint operators.
-- source:
--   A Minkowski Type Trace Inequality and Strong Subadditivity of Quantum Entropy II: Convexity and Concavity, arXiv:0710.4167v3, PDF p. 5, Unnumbered main result

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P28

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Dependency50.P35
  (spectralPower tr leftMarginal rightMarginal marginalAC)

namespace QAlgorithms.Papers.Independent.Intake100.P28

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Equation (1.12), PDF pp.5–6: all real norm axioms on self-adjoint matrices. -/
theorem selfAdjointNorm {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (p q : ℝ) (hp : 1 ≤ p) (hp2 : p ≤ 2) (hq : 1 ≤ q) :
    IsHermitianNorm (selfAdjointGauge (I := Fin m) (J := Fin n) p q) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P28

end
