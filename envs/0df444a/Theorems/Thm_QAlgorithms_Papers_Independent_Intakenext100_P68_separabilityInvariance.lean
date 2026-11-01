-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P68_separabilityInvariance
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P68.separabilityInvariance
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:30:28.433781+00:00
-- url     : https://prove2.me/theorems/3c043407-4fce-4f8b-bfe9-84001dc574a2
-- title:
--   Separability is invariant at every positive iteration
-- statement:
--   Let $n,m\ge1$ be finite local mode counts, with interleaved quadratures $(X_1,P_1,\ldots)$, $[X_j,P_j]=i$, and doubled covariance $\gamma_{ab}=2\operatorname{Re}\langle(R_a-d_a)(R_b-d_b)\rangle$. Thus vacuum covariance is $I$. Put $J_r=\bigoplus_{j=1}^r\begin{pmatrix}0&-1\\1&0\end{pmatrix}$. A covariance matrix (CM) is real symmetric and satisfies $\gamma-iJ\succeq0$. All inequalities below are Loewner inequalities.
--
--   Let $\gamma_0=\begin{pmatrix}A_0&C_0\\C_0^T&B_0\end{pmatrix}$ be a physical $n|m$ CM. Construct the sequence as follows: a nonphysical matrix is followed by zero; otherwise put $X_j=C_j(B_j-iJ)^+C_j^T$, $A_{j+1}=B_{j+1}=A_j-\operatorname{Re}X_j$, and $C_{j+1}=-\operatorname{Im}X_j$. All inverses are spectral Moore–Penrose inverses. Every positive-index matrix has split $n|n$. Set $L_j=A_j-\|C_j\|_{\mathrm{op}}I$ for $j\ge1$, where the norm is Euclidean induced. Separability always means the trace-norm closed convex hull of full oscillator product densities, independently of covariance witness inequalities.
--
--   Say that a bipartite covariance is separable when it is the covariance of some actual normalized separable Gaussian density, with arbitrary first moments. For every individual $N\ge1$,
--
--   $$
--   \gamma_0\text{ is separable}\quad\Longleftrightarrow\quad\gamma_N\text{ is separable}.
--   $$
--
--   The right-hand side includes validity as a physical covariance. This relates the constructed iterates to full state separability rather than defining separability by matrix witnesses.
-- source:
--   Separability Criterion for all bipartite Gaussian States, arXiv:quant-ph/0104050v1, PDF p. 2, Unnumbered result immediately before Theorem 1

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

/-- PDF p.2 immediately above Thm.1: separability of actual Gaussian densities
is invariant at every individual positive iteration, including physicality. -/
theorem separabilityInvariance {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (g : CovarianceBlocks n m) (hg : IsPhysicalCovariance g) :
    ∀ k : ℕ, SeparableCM g ↔ SeparableCM (tail g k) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P68

end
