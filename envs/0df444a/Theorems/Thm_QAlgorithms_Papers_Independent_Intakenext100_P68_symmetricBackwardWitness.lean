-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P68_symmetricBackwardWitness
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P68.symmetricBackwardWitness
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:29:46.395324+00:00
-- url     : https://prove2.me/theorems/11fc195f-c9ac-45bd-90d7-718d608d890b
-- title:
--   Symmetric local witness from backward transport
-- statement:
--   Let $n,m\ge1$ be finite local mode counts, with interleaved quadratures $(X_1,P_1,\ldots)$, $[X_j,P_j]=i$, and doubled covariance $\gamma_{ab}=2\operatorname{Re}\langle(R_a-d_a)(R_b-d_b)\rangle$. Thus vacuum covariance is $I$. Put $J_r=\bigoplus_{j=1}^r\begin{pmatrix}0&-1\\1&0\end{pmatrix}$. A covariance matrix (CM) is real symmetric and satisfies $\gamma-iJ\succeq0$. All inequalities below are Loewner inequalities.
--
--   Let $\gamma_0=\begin{pmatrix}A_0&C_0\\C_0^T&B_0\end{pmatrix}$ be a physical $n|m$ CM. Construct the sequence as follows: a nonphysical matrix is followed by zero; otherwise put $X_j=C_j(B_j-iJ)^+C_j^T$, $A_{j+1}=B_{j+1}=A_j-\operatorname{Re}X_j$, and $C_{j+1}=-\operatorname{Im}X_j$. All inverses are spectral Moore–Penrose inverses. Every positive-index matrix has split $n|n$. Set $L_j=A_j-\|C_j\|_{\mathrm{op}}I$ for $j\ge1$, where the norm is Euclidean induced. Separability always means the trace-norm closed convex hull of full oscillator product densities, independently of covariance witness inequalities.
--
--   Let $N\ge1$ and let $U$ be a CM such that $\gamma_{N+1}\succeq U\oplus U$. Construct $V=B_N-C_N^T(A_N-U)^+C_N$ and $\widetilde U=(U+V)/2$. Then
--
--   $$
--   \widetilde U\text{ is a CM},\qquad\gamma_N\succeq\widetilde U\oplus\widetilde U.
--   $$
--
--   This provides the symmetric witness needed in the positive-index backward recursion.
-- source:
--   Separability Criterion for all bipartite Gaussian States, arXiv:quant-ph/0104050v1, PDF p. 2, Corollary 1

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

/-- PDF p.2, Corollary 1: N=k+1 >= 1. The second witness is the corrected
constructed Eq.(5) object, not an independently quantified matrix. -/
theorem symmetricBackwardWitness {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (g : CovarianceBlocks n m) (hg : IsPhysicalCovariance g) (k : ℕ) (U : Cov n)
    (hU : IsCM U) (hdom : DominatesLocalCovariances (tail g (k + 1)) U U) :
    IsCM (averageWitness (tail g k) U) ∧
      DominatesLocalCovariances (tail g k) (averageWitness (tail g k) U)
        (averageWitness (tail g k) U) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P68

end
