-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P68_pureProductDecomposition
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P68.pureProductDecomposition
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:32:03.130713+00:00
-- url     : https://prove2.me/theorems/13dc91fc-e624-43c2-9992-62ef04425ef4
-- title:
--   Pure-product probability ensemble for every separable Gaussian density
-- statement:
--   Let $n,m\ge1$ be finite local mode counts, with interleaved quadratures $(X_1,P_1,\ldots)$, $[X_j,P_j]=i$, and doubled covariance $\gamma_{ab}=2\operatorname{Re}\langle(R_a-d_a)(R_b-d_b)\rangle$. Thus vacuum covariance is $I$. Put $J_r=\bigoplus_{j=1}^r\begin{pmatrix}0&-1\\1&0\end{pmatrix}$. A covariance matrix (CM) is real symmetric and satisfies $\gamma-iJ\succeq0$. All inequalities below are Loewner inequalities.
--
--   Let $\gamma_0=\begin{pmatrix}A_0&C_0\\C_0^T&B_0\end{pmatrix}$ be a physical $n|m$ CM. Construct the sequence as follows: a nonphysical matrix is followed by zero; otherwise put $X_j=C_j(B_j-iJ)^+C_j^T$, $A_{j+1}=B_{j+1}=A_j-\operatorname{Re}X_j$, and $C_{j+1}=-\operatorname{Im}X_j$. All inverses are spectral Moore–Penrose inverses. Every positive-index matrix has split $n|n$. Set $L_j=A_j-\|C_j\|_{\mathrm{op}}I$ for $j\ge1$, where the norm is Euclidean induced. Separability always means the trace-norm closed convex hull of full oscillator product densities, independently of covariance witness inequalities.
--
--   Let $\rho$ be an actual normalized separable Gaussian density of covariance $\gamma_0$ and arbitrary first moments. On the product of the two local pure-density spaces, each carrying its trace-norm Borel structure, there is a probability measure $\mu$ such that
--
--   $$
--   \rho=\int \pi_A\otimes\pi_B\,d\mu(\pi_A,\pi_B).
--   $$
--
--   The equality is expressed by all operator coefficients, with each scalar integrand integrable. Pure densities are rank-one projectors onto norm-one vectors. The ensemble may be continuous and is not required to have Gaussian factors. This is the full density decomposition promised by the abstract, with its final construction credited to [7].
-- source:
--   Separability Criterion for all bipartite Gaussian States, arXiv:quant-ph/0104050v1, PDF p. 1, Abstract; construction attributed to [7] on pp.1–2

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P68

noncomputable section

open MeasureTheory Filter

open scoped BigOperators Topology ComplexOrder

namespace QAlgorithms.Papers.Independent.Intakenext100.P68

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State PureState IsSeparable IsBarycenter productCoeff)

open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify)

open QAlgorithms.Papers.Independent.Frontier30.P08 (QuadratureIndex)

open QAlgorithms.Papers.Independent.Claimed50.P19 (Cov)

open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)

/-- PDF p.1 abstract, via pp.1--2 attribution to [7]: Borel probability ensemble
of pure product states on full oscillator spaces. The law may be continuous;
no finite/countable ensemble or Gaussian factors are asserted. Integrability
is included in the accepted barycenter predicate. -/
theorem pureProductDecomposition {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (g : CovarianceBlocks n m) (rho : State (Occupation (Fin n) × Occupation (Fin m)))
    (d : QuadratureIndex n ⊕ QuadratureIndex m → ℝ) (hG : HasGaussianCovariance rho g d)
    (hsep : IsSeparable rho.coefficients) :
    ∃ mu : Measure (PureState (Occupation (Fin n)) × PureState (Occupation (Fin m))),
      IsProbabilityMeasure mu ∧
      IsBarycenter mu
        (fun p => productCoeff p.1.val.coefficients p.2.val.coefficients)
        rho.coefficients := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P68

end
