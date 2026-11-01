-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P68_strongerThanPartialTransposition
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P68.strongerThanPartialTransposition
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:34:34.066085+00:00
-- url     : https://prove2.me/theorems/ba47da20-c123-4fc7-a68f-452eaa72f6a9
-- title:
--   The criterion detects a PPT-entangled Gaussian input
-- statement:
--   Let $n,m\ge1$ be finite local mode counts, with interleaved quadratures $(X_1,P_1,\ldots)$, $[X_j,P_j]=i$, and doubled covariance $\gamma_{ab}=2\operatorname{Re}\langle(R_a-d_a)(R_b-d_b)\rangle$. Thus vacuum covariance is $I$. Put $J_r=\bigoplus_{j=1}^r\begin{pmatrix}0&-1\\1&0\end{pmatrix}$. A covariance matrix (CM) is real symmetric and satisfies $\gamma-iJ\succeq0$. All inequalities below are Loewner inequalities.
--
--   Let $\gamma_0=\begin{pmatrix}A_0&C_0\\C_0^T&B_0\end{pmatrix}$ be a physical $n|m$ CM. Construct the sequence as follows: a nonphysical matrix is followed by zero; otherwise put $X_j=C_j(B_j-iJ)^+C_j^T$, $A_{j+1}=B_{j+1}=A_j-\operatorname{Re}X_j$, and $C_{j+1}=-\operatorname{Im}X_j$. All inverses are spectral Moore–Penrose inverses. Every positive-index matrix has split $n|n$. Set $L_j=A_j-\|C_j\|_{\mathrm{op}}I$ for $j\ge1$, where the norm is Euclidean induced. Separability always means the trace-norm closed convex hull of full oscillator product densities, independently of covariance witness inequalities.
--
--   There exist positive finite mode counts $n,m$, a normalized Gaussian density $\rho$ with physical covariance $\gamma_0$ and arbitrary mean, and an integer $N\ge1$ such that
--
--   $$
--   \gamma_0^{T_B}\succeq iJ,\qquad
--   \rho\text{ is not separable},\qquad A_N\not\succeq iJ.
--   $$
--
--   The covariance partial transpose reverses the second party's momentum coordinates and preserves its position coordinates. Thus some PPT-entangled Gaussian input is detected by the nonlinear criterion. The input example is background from Werner–Wolf [7]; no floating-point threshold is asserted as exact.
-- source:
--   Separability Criterion for all bipartite Gaussian States, arXiv:quant-ph/0104050v1, PDF p. 1, Abstract; pp.2–3 and Fig.1b

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

/-- PDF p.1 abstract and pp.2--3, Fig.1b: some PPT-entangled Gaussian input
is detected. The example's provenance is [7]. No decimal threshold or universal
iteration count is extracted from numerical data. -/
theorem strongerThanPartialTransposition :
    ∃ n m : ℕ, 0 < n ∧ 0 < m ∧
      ∃ (g : CovarianceBlocks n m) (rho : State (Occupation (Fin n) × Occupation (Fin m)))
        (d : QuadratureIndex n ⊕ QuadratureIndex m → ℝ),
        HasGaussianCovariance rho g d ∧ IsPhysicalCovariance (partialTransposeCovariance g) ∧
        ¬ IsSeparable rho.coefficients ∧
        ∃ k : ℕ, ¬ Uncertainty (tail g k).A := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P68

end
