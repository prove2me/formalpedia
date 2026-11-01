-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P68_forwardTransport
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P68.forwardTransport
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:28:19.787754+00:00
-- url     : https://prove2.me/theorems/401aff44-193d-4e86-bc77-2a7bbf69eee0
-- title:
--   Forward transport of physical local covariance witnesses
-- statement:
--   Let $n,m\ge1$ be finite local mode counts, with interleaved quadratures $(X_1,P_1,\ldots)$, $[X_j,P_j]=i$, and doubled covariance $\gamma_{ab}=2\operatorname{Re}\langle(R_a-d_a)(R_b-d_b)\rangle$. Thus vacuum covariance is $I$. Put $J_r=\bigoplus_{j=1}^r\begin{pmatrix}0&-1\\1&0\end{pmatrix}$. A covariance matrix (CM) is real symmetric and satisfies $\gamma-iJ\succeq0$. All inequalities below are Loewner inequalities.
--
--   Let $\gamma_0=\begin{pmatrix}A_0&C_0\\C_0^T&B_0\end{pmatrix}$ be a physical $n|m$ CM. Construct the sequence as follows: a nonphysical matrix is followed by zero; otherwise put $X_j=C_j(B_j-iJ)^+C_j^T$, $A_{j+1}=B_{j+1}=A_j-\operatorname{Re}X_j$, and $C_{j+1}=-\operatorname{Im}X_j$. All inverses are spectral Moore–Penrose inverses. Every positive-index matrix has split $n|n$. Set $L_j=A_j-\|C_j\|_{\mathrm{op}}I$ for $j\ge1$, where the norm is Euclidean induced. Separability always means the trace-norm closed convex hull of full oscillator product densities, independently of covariance witness inequalities.
--
--   For each $N\ge0$, let $U$ and $V$ be local CMs of the corresponding block sizes: $U$ has $n$ modes and $V$ has $m$ modes at $N=0$, or $n$ modes at $N\ge1$. Then
--
--   $$
--   \gamma_N\succeq U\oplus V\quad\Longrightarrow\quad\gamma_{N+1}\succeq U\oplus U.
--   $$
--
--   This transports local witnesses forward, without requiring strict positivity or invertibility.
-- source:
--   Separability Criterion for all bipartite Gaussian States, arXiv:quant-ph/0104050v1, PDF p. 2, Proposition 1

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

/-- PDF p.2, Proposition 1, for N=0 and N=k+1 respectively.
Both local witnesses are CMs; singular matrices are included. -/
theorem forwardTransport {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (g : CovarianceBlocks n m) (hg : IsPhysicalCovariance g) :
    (∀ (U : Cov n) (V : Cov m), IsCM U → IsCM V → DominatesLocalCovariances g U V →
      DominatesLocalCovariances (covarianceStep g) U U) ∧
    (∀ (k : ℕ) (U V : Cov n), IsCM U → IsCM V →
      DominatesLocalCovariances (tail g k) U V → DominatesLocalCovariances (tail g (k + 1)) U U) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P68

end
