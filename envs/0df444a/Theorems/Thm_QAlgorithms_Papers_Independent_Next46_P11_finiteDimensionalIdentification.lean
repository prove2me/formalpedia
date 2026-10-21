-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P11_finiteDimensionalIdentification
-- name    : QAlgorithms.Papers.Independent.Next46.P11.finiteDimensionalIdentification
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T13:03:11.792426+00:00
-- url     : https://prove2.me/theorems/146d4fab-3c4e-4da8-9a16-936438d60c7b
-- title:
--   Finite-dimensional identification of Araki–Masuda and sandwiched Rényi divergences
-- statement:
--   Let $n\ge1$, let $R$ be a positive semidefinite $n\times n$ complex matrix with $\operatorname{Tr}R=1$, and let $S$ be any positive semidefinite matrix. The reference $S$ need not be normalized or invertible. Let $\alpha\in[\tfrac12,1)\cup(1,\infty)$. In the standard matrix representation, define $\|\sqrt R\|_{p,S}$ by the supremum or infimum in Definition 2, using the spatial-power formula (10), with $p=2\alpha$. Thus this is a norm of the implementing vector $\sqrt R$, rather than of $R$ itself. Put $Q_\alpha=\|\sqrt R\|_{2\alpha,S}^{2\alpha}$ and $D_\alpha^{\mathrm{AM}}=(\alpha-1)^{-1}\log Q_\alpha$.
--
--   Then
--
--   $$
--   D_\alpha^{\mathrm{AM}}(R\|S)=\begin{cases}
--   +\infty,&\alpha>1\text{ and }\operatorname{supp}R\not\le\operatorname{supp}S,\\
--   \displaystyle\frac{1}{\alpha-1}\log\operatorname{Tr}\!\left(S^{\frac{1-\alpha}{2\alpha}}R S^{\frac{1-\alpha}{2\alpha}}\right)^\alpha,&\text{otherwise}.
--   \end{cases}
--   $$
--
--   All matrix powers are spectral powers taken on their supports and zero on their kernels. Logarithms are natural, with $\log0=-\infty$ and $\log(+\infty)=+\infty$. This identifies the finite matrix instance of the algebraic divergence with the sandwiched Rényi divergence.
--
--   **Formalization Note** The left side is constructed from an optimization over positive trace-one matrices, independently of the trace formula on the right. The finite matrix representation is the $M_n$ representation fixed in the source on p.3; no general-algebra theorem is replaced by a matrix special case.
-- source:
--   R\'enyi divergences as weighted non-commutative vector valued $L_p$-spaces, arXiv:1608.05317v2, PDF p. 9, §4.1 Eq.(39); Definition 2 and Eq.(10), p.5; Definition 7, p.8

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P11

noncomputable section

open scoped BigOperators ENNReal Matrix ComplexOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Next46.P11

attribute [local instance] Classical.propDecidable

/-- Eq.(39), PDF p.9, with Definition 2 and Eq.(10) on p.5 and Definition 7
on p.8: the finite-dimensional Araki--Masuda divergence is the sandwiched
Renyi divergence. rho has trace one; sigma is arbitrary positive semidefinite,
including zero. The support-failure infinity branch for alpha > 1 is inherited
from Eq.(8), as specified by the source's definition. -/
theorem finiteDimensionalIdentification
    (n : ℕ) (hDimension : 0 < n)
    (rho sigma : Matrix (Fin n) (Fin n) ℂ)
    (hRho : IsMatrixDensity rho) (hSigma : sigma.PosSemidef)
    (alpha : ℝ) (hAlpha : 1 / 2 ≤ alpha) (hAlphaNeOne : alpha ≠ 1) :
    finiteAMDivergence rho sigma alpha =
      if 1 < alpha ∧ ¬ MatrixSupportIncluded rho sigma then ⊤ else
        let S := supportedMatrixPower sigma ((1 - alpha) / (2 * alpha))
        ((1 / (alpha - 1) : ℝ) : EReal) *
          ENNReal.log (ENNReal.ofReal
            ((supportedMatrixPower (S * rho * S) alpha).trace.re)) := by sorry

end QAlgorithms.Papers.Independent.Next46.P11

end
