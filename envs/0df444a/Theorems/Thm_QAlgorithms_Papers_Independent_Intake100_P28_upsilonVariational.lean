-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P28_upsilonVariational
-- name    : QAlgorithms.Papers.Independent.Intake100.P28.upsilonVariational
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:31:06.011425+00:00
-- url     : https://prove2.me/theorems/d7b8901d-f124-45f7-9cbc-b607e541fcd0
-- title:
--   Lemma 2.2: infimum and supremum variational formulas
-- statement:
--   Let $n,m$ be positive integers. All matrices are complex and positive semidefinite unless otherwise specified, including singular matrices and zero. For $p,q>0$, put
--   $$
--   \Phi_{p,q}(A_1,\ldots,A_m)=\left(\operatorname{Tr}(\sum_j A_j^p)^{q/p}\right)^{1/q},\quad
--   \Psi_{p,q}(A)=\left(\operatorname{Tr}(\operatorname{Tr}_2 A^p)^{q/p}\right)^{1/q},\quad
--   \Upsilon_{p,q}^{B}(A)=\operatorname{Tr}(B^*A^pB)^{q/p}.
--   $$
--   Here powers are spectral powers, $B$ is an arbitrary fixed complex matrix, and $\operatorname{Tr}_2$ is the unnormalized partial trace over the second factor of $\mathbb C^m\otimes\mathbb C^n$. Convexity and concavity use every mixture weight in $[0,1]$.
--
--   For $A\ge0$, put $r=p/q>0$ and, for positive definite $X$, define
--   $$
--   F_{p,q}^{B,A}(X)=\operatorname{Tr}\left[A^{p/2}B X^{1-r}B^*A^{p/2}+(r-1)X\right].
--   $$
--   The following variational identities hold:
--   $$
--   r>1:\quad\Upsilon_{p,q}^{B}(A)=\frac1r\inf_{X>0}F_{p,q}^{B,A}(X),\qquad
--   0<r<1:\quad\Upsilon_{p,q}^{B}(A)=\frac1r\sup_{X>0}F_{p,q}^{B,A}(X).
--   $$
--   Both extrema are over all positive definite complex $n\times n$ matrices. No attainment is asserted; in particular, $B=0$ is included. The $r=1$ case is not claimed by these two formulas.
--
--   These identities are the variational bridge used to obtain convexity and concavity of $\Upsilon$.
-- source:
--   A Minkowski Type Trace Inequality and Strong Subadditivity of Quantum Entropy II: Convexity and Concavity, arXiv:0710.4167v3, PDF p. 8, Lemma 2.2

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P28

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Dependency50.P35
  (spectralPower tr leftMarginal rightMarginal marginalAC)

namespace QAlgorithms.Papers.Independent.Intake100.P28

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Lemma 2.2, PDF p.8: (2.5)–(2.6). X>0 is definite; no attainment is claimed.
The exponent is 1-r, not -1/(r-1); B precedes the inverse power. -/
theorem upsilonVariational {n : ℕ} (hn : 0 < n) (p q : ℝ)
    (hp : 0 < p) (hq : 0 < q) (B A : Mat (Fin n)) (hA : A.PosSemidef) :
    (1 < p / q → sandwichedTraceFunctional p q B A = (1 / (p / q)) *
      sInf {v : ℝ | ∃ X : Mat (Fin n), X.PosDef ∧ v = variationalObjective p q B A X}) ∧
    (p / q < 1 → sandwichedTraceFunctional p q B A = (1 / (p / q)) *
      sSup {v : ℝ | ∃ X : Mat (Fin n), X.PosDef ∧ v = variationalObjective p q B A X}) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P28

end
