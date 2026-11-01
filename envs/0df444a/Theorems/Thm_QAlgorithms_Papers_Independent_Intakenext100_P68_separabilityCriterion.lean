-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P68_separabilityCriterion
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P68.separabilityCriterion
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:27:34.289738+00:00
-- url     : https://prove2.me/theorems/129a9b43-49a1-4cf5-9157-a36189d585df
-- title:
--   Two separability certificates along the Gaussian covariance iteration
-- statement:
--   Let $n,m\ge1$ be finite local mode counts, with interleaved quadratures $(X_1,P_1,\ldots)$, $[X_j,P_j]=i$, and doubled covariance $\gamma_{ab}=2\operatorname{Re}\langle(R_a-d_a)(R_b-d_b)\rangle$. Thus vacuum covariance is $I$. Put $J_r=\bigoplus_{j=1}^r\begin{pmatrix}0&-1\\1&0\end{pmatrix}$. A covariance matrix (CM) is real symmetric and satisfies $\gamma-iJ\succeq0$. All inequalities below are Loewner inequalities.
--
--   Let $\gamma_0=\begin{pmatrix}A_0&C_0\\C_0^T&B_0\end{pmatrix}$ be a physical $n|m$ CM. Construct the sequence as follows: a nonphysical matrix is followed by zero; otherwise put $X_j=C_j(B_j-iJ)^+C_j^T$, $A_{j+1}=B_{j+1}=A_j-\operatorname{Re}X_j$, and $C_{j+1}=-\operatorname{Im}X_j$. All inverses are spectral Moore–Penrose inverses. Every positive-index matrix has split $n|n$. Set $L_j=A_j-\|C_j\|_{\mathrm{op}}I$ for $j\ge1$, where the norm is Euclidean induced. Separability always means the trace-norm closed convex hull of full oscillator product densities, independently of covariance witness inequalities.
--
--   Let $\rho$ be any actual normalized Gaussian density of covariance $\gamma_0$ and arbitrary first moments. Then both implications hold:
--
--   $$
--   (\exists N\ge1:\ A_N\not\succeq iJ)\Longrightarrow\rho\text{ is not separable},\qquad
--   (\exists N\ge1:\ L_N\succeq iJ)\Longrightarrow\rho\text{ is separable}.
--   $$
--
--   These are sound rejection and acceptance certificates. They do not assert finite termination for every input.
-- source:
--   Separability Criterion for all bipartite Gaussian States, arXiv:quant-ph/0104050v1, PDF p. 2, Theorem 1 (Separability criterion)

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

/-- PDF p.2, Theorem 1, BOTH certificates, for an actual normalized Gaussian
input with arbitrary first moments. Tail k means N=k+1 >= 1. No termination,
invertibility, local-witness-existence or separability assumption is added. -/
theorem separabilityCriterion {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (g : CovarianceBlocks n m) (rho : State (Occupation (Fin n) × Occupation (Fin m)))
    (d : QuadratureIndex n ⊕ QuadratureIndex m → ℝ) (hG : HasGaussianCovariance rho g d) :
    ((∃ k : ℕ, ¬ Uncertainty (tail g k).A) → ¬ IsSeparable rho.coefficients) ∧
    ((∃ k : ℕ, Uncertainty (lowerWitness (tail g k))) →
      IsSeparable rho.coefficients) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P68

end
