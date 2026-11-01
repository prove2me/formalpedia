-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P68_witnessReconstruction
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P68.witnessReconstruction
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:31:13.642108+00:00
-- url     : https://prove2.me/theorems/d6423ee1-c742-4f99-899d-41da00d27bf3
-- title:
--   Reconstruct original local witnesses by the specified backward recursion
-- statement:
--   Let $n,m\ge1$ be finite local mode counts, with interleaved quadratures $(X_1,P_1,\ldots)$, $[X_j,P_j]=i$, and doubled covariance $\gamma_{ab}=2\operatorname{Re}\langle(R_a-d_a)(R_b-d_b)\rangle$. Thus vacuum covariance is $I$. Put $J_r=\bigoplus_{j=1}^r\begin{pmatrix}0&-1\\1&0\end{pmatrix}$. A covariance matrix (CM) is real symmetric and satisfies $\gamma-iJ\succeq0$. All inequalities below are Loewner inequalities.
--
--   Let $\gamma_0=\begin{pmatrix}A_0&C_0\\C_0^T&B_0\end{pmatrix}$ be a physical $n|m$ CM. Construct the sequence as follows: a nonphysical matrix is followed by zero; otherwise put $X_j=C_j(B_j-iJ)^+C_j^T$, $A_{j+1}=B_{j+1}=A_j-\operatorname{Re}X_j$, and $C_{j+1}=-\operatorname{Im}X_j$. All inverses are spectral Moore–Penrose inverses. Every positive-index matrix has split $n|n$. Set $L_j=A_j-\|C_j\|_{\mathrm{op}}I$ for $j\ge1$, where the norm is Euclidean induced. Separability always means the trace-norm closed convex hull of full oscillator product densities, independently of covariance witness inequalities.
--
--   Suppose $N\ge1$ and $L_N\succeq iJ$. Initialize $U_N=L_N$ and, in descending order $j=N-1,\ldots,1$, define
--
--   $$
--   V_j=B_j-C_j^T(A_j-U_{j+1})^+C_j,\qquad U_j=\frac{U_{j+1}+V_j}{2}.
--   $$
--
--   Finally put $U=U_1$ and $V=B_0-C_0^T(A_0-U)^+C_0$. Then
--
--   $$
--   U\text{ and }V\text{ are CMs},\qquad\gamma_0\succeq U\oplus V.
--   $$
--
--   For $N=1$ the descending loop is empty. The statement specifies the witnesses constructed by the paper, rather than merely asserting existence.
-- source:
--   Separability Criterion for all bipartite Gaussian States, arXiv:quant-ph/0104050v1, PDF p. 2, Construction following Theorem 1

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

/-- PDF p.2 following Thm.1: explicit backward recursion from terminal
L_(k+1), then corrected Prop.2 at gamma_0, recovers both original local CMs. -/
theorem witnessReconstruction {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (g : CovarianceBlocks n m) (hg : IsPhysicalCovariance g) (k : ℕ)
    (hstop : Uncertainty (lowerWitness (tail g k))) :
    let U := recoverFirst g k (lowerWitness (tail g k))
    let V := secondWitness g U
    IsCM U ∧ IsCM V ∧ DominatesLocalCovariances g U V := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P68

end
