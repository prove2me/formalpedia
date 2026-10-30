-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P28_corollary37
-- name    : QAlgorithms.Papers.Independent.Extend50.P28.corollary37
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T08:13:15.504836+00:00
-- url     : https://prove2.me/theorems/671dfe7e-5d71-407f-80b0-0a773465190a
-- title:
--   Content eigenvalues in terms of actual tensor multiplicities
-- statement:
--   Let $n,d\ge2$, let $H=(\mathbb C^d)^{\otimes n}$ with its fixed computational orthonormal basis, and put $N=n-1$. For $a=1,\ldots,N$, let $T_a$ be the last-factor partial transpose of the tensor permutation swapping $a$ and $n$, and put $\rho=\sum_aT_a$. Write $d_\eta$ for the actual Specht dimension and $m_\eta$ for the multiplicity of that Specht module in the appropriate tensor permutation representation; these are defined by dimensions of actual intertwiner spaces. Let $\alpha\vdash n-2$ have at most $d$ rows, and let $\nu\vdash n-1$ be any one-box extension of $\alpha$, including a possible extension with $d+1$ rows. Let $\lambda_\nu(\alpha)=d+c(\nu/\alpha)$, where content is column minus row. Then
--
--   $$
--   \lambda_\nu(\alpha)=(n-1)\frac{m_\nu d_\alpha}{m_\alpha d_\nu}.
--   $$
--
--   The physical lower shape ensures $m_\alpha>0$, and $d_\nu>0$ for every upper shape. An upper shape of height $d+1$ has $m_\nu=0$ and eigenvalue zero; it is included.
-- source:
--   Simplified formalism of the algebra of partially transposed permutation operators with applications, arXiv:1708.02434v2, PDF p. 16, Corollary 37

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P28

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P28

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

local notation "Shape" => (fun k : ℕ => QAlgorithms.Schur.Partition k k)

local notation "Word" => (fun d n : ℕ => Fin n → Fin d)

/-- PDF p.16, Corollary 37, Eq.(72). Printed d_mu is changed to d_nu:
mu is unbound, and (67),(71),(102) uniquely force the latter index.
The upper label ranges over every one-box extension, including the possible zero
Gram branch of height d+1; its actual tensor multiplicity is zero. Only alpha
needs physical height at most d to keep the denominator nonzero. -/
theorem corollary37 (n d : ℕ) (hn : 2 ≤ n) (hd : 2 ≤ d)
    (alpha : QAlgorithms.Schur.Partition d (n - 2))
    (nu : QAlgorithms.Schur.Partition (n - 1) (n - 1))
    (hbranch : alpha.val.cells ⊆ nu.val.cells) :
    contentEigenvalue d alpha.val nu.val =
      ((n : ℝ) - 1) * (tensorMultiplicity d nu : ℝ) * (irrepDim alpha : ℝ) /
        ((tensorMultiplicity d alpha : ℝ) * (irrepDim nu : ℝ)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P28

end
