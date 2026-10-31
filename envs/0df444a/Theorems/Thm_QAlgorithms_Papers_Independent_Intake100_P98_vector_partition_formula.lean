-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P98_vector_partition_formula
-- name    : QAlgorithms.Papers.Independent.Intake100.P98.vector_partition_formula
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T16:05:41.000856+00:00
-- url     : https://prove2.me/theorems/5c3559cf-c39a-425a-8e42-438eec4cd5a9
-- title:
--   Theorem 2.3: an actual vector partition function for LR coefficients
-- statement:
--   Let $k\ge1$. A partition is a weakly decreasing $k$-tuple of nonnegative integers, padded by zeros. For a triple $x=(\lambda,\mu,\nu)$ assume $|\lambda|+|\mu|=|\nu|$ and $\lambda_i,\mu_i\le\nu_i$ for every $i$, where $|\lambda|=\sum_i\lambda_i$. Write $c^\nu_{\lambda\mu}$ for the ordinary homogeneous Littlewood–Richardson coefficient.
--
--   Substitute the hive boundary sums (20) into the three rhombus inequalities (17)–(19). Write the resulting system as $Aa\le B_kx$, with interior indices $i,j\ge1$, $i+j\le k-1$, and append nonnegative slack variables to obtain $E_k=[A\mid I]$. These are the matrices constructed from the inequalities, with rows labelled by orientation and origin. For these matrices,
--
--   $$
--   \ker(E_k)\cap\mathbb R_{\ge0}^{\,\operatorname{cols}(E_k)}=\{0\},\qquad
--   c^\nu_{\lambda\mu}=\varphi_{E_k}(B_kx),
--   \qquad
--   \varphi_M(b)=\#\{a\in\mathbb N^{\operatorname{cols}(M)}:Ma=b\}.
--   $$
--
--   The fiber is finite. This identifies the LR coefficient with an actual vector partition count, not with a matrix whose defining fields postulate the desired equality.
-- source:
--   A polynomiality property for Littlewood-Richardson coefficients, arXiv:math/0308101v2, PDF p. 7, Theorem 2.3: an actual vector partition function for LR coefficients

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P98

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Intake100.P98

open QAlgorithms.Papers.Independent.Frontier30.P19

attribute [local instance] Classical.propDecidable

/-- Theorem 2.3, PDF p.7. E_k and B_k are the actual matrices (22)--(24),
not existential witnesses. Pointedness is asserted, not hypothesized; it ensures
that Nat.card counts a finite fiber rather than defaulting to zero on infinity. -/
theorem vector_partition_formula (k : ℕ) (hk : 0 < k) :
    PointedKernel (hiveMatrix k) ∧
    ∀ x : Coordinates k → ℕ, IntegralDomain x →
      Finite (partitionFiber (hiveMatrix k) (boundaryRhs x)) ∧
      paddedLRCoefficient x = vectorPartition (hiveMatrix k) (boundaryRhs x) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P98

end
