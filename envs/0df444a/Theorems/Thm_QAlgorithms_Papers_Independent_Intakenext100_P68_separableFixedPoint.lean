-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P68_separableFixedPoint
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P68.separableFixedPoint
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:34:01.861101+00:00
-- url     : https://prove2.me/theorems/ceab0f84-e323-4799-a169-f3a0d7b8ebe8
-- title:
--   Convergence of every separable input to an equal-block fixed point
-- statement:
--   Let $n,m\ge1$ be finite local mode counts, with interleaved quadratures $(X_1,P_1,\ldots)$, $[X_j,P_j]=i$, and doubled covariance $\gamma_{ab}=2\operatorname{Re}\langle(R_a-d_a)(R_b-d_b)\rangle$. Thus vacuum covariance is $I$. Put $J_r=\bigoplus_{j=1}^r\begin{pmatrix}0&-1\\1&0\end{pmatrix}$. A covariance matrix (CM) is real symmetric and satisfies $\gamma-iJ\succeq0$. All inequalities below are Loewner inequalities.
--
--   Let $\gamma_0=\begin{pmatrix}A_0&C_0\\C_0^T&B_0\end{pmatrix}$ be a physical $n|m$ CM. Construct the sequence as follows: a nonphysical matrix is followed by zero; otherwise put $X_j=C_j(B_j-iJ)^+C_j^T$, $A_{j+1}=B_{j+1}=A_j-\operatorname{Re}X_j$, and $C_{j+1}=-\operatorname{Im}X_j$. All inverses are spectral Moore–Penrose inverses. Every positive-index matrix has split $n|n$. Set $L_j=A_j-\|C_j\|_{\mathrm{op}}I$ for $j\ge1$, where the norm is Euclidean induced. Separability always means the trace-norm closed convex hull of full oscillator product densities, independently of covariance witness inequalities.
--
--   If $\gamma_0$ is separable as an actual Gaussian covariance, then there is an $n$-mode CM $U$ such that
--
--   $$
--   \lim_{N\to\infty,\ N\ge1}\gamma_N=U\oplus U,
--   \qquad f(U\oplus U)=U\oplus U,
--   $$
--
--   where $f$ is the source's one-step covariance map. Convergence is in the usual finite-matrix topology. There is no strict margin, convergence rate or finite stopping hypothesis. Only the positive-index tail is placed in a single fixed-size space.
-- source:
--   Separability Criterion for all bipartite Gaussian States, arXiv:quant-ph/0104050v1, PDF p. 3, Paragraph following Proposition 3, spanning both columns

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

/-- PDF p.3, bottom-left paragraph continued top-right: all separable inputs
converge to diag(Ainf,Ainf), a physical fixed point. No strict margin, rate or
finite stopping is assumed. Convergence uses only the fixed-size positive tail. -/
theorem separableFixedPoint {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (g : CovarianceBlocks n m) (hg : IsPhysicalCovariance g) (hsep : SeparableCM g) :
    ∃ U : Cov n, IsCM U ∧
      Tendsto (fun k : ℕ => covarianceBlockMatrix (tail g k)) atTop
        (nhds (realCovarianceSum U U)) ∧
      covarianceStep ({ A := U, B := U, C := 0 } : CovarianceBlocks n n) =
        ({ A := U, B := U, C := 0 } : CovarianceBlocks n n) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P68

end
