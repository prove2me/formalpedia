-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P68_strictMarginFiniteStopping
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P68.strictMarginFiniteStopping
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:32:35.981223+00:00
-- url     : https://prove2.me/theorems/5753137f-b9f2-4c9b-9c54-3d9db5ecc4c9
-- title:
--   Finite stopping under a strict local uncertainty margin
-- statement:
--   Let $n,m\ge1$ be finite local mode counts, with interleaved quadratures $(X_1,P_1,\ldots)$, $[X_j,P_j]=i$, and doubled covariance $\gamma_{ab}=2\operatorname{Re}\langle(R_a-d_a)(R_b-d_b)\rangle$. Thus vacuum covariance is $I$. Put $J_r=\bigoplus_{j=1}^r\begin{pmatrix}0&-1\\1&0\end{pmatrix}$. A covariance matrix (CM) is real symmetric and satisfies $\gamma-iJ\succeq0$. All inequalities below are Loewner inequalities.
--
--   Let $\gamma_0=\begin{pmatrix}A_0&C_0\\C_0^T&B_0\end{pmatrix}$ be a physical $n|m$ CM. Construct the sequence as follows: a nonphysical matrix is followed by zero; otherwise put $X_j=C_j(B_j-iJ)^+C_j^T$, $A_{j+1}=B_{j+1}=A_j-\operatorname{Re}X_j$, and $C_{j+1}=-\operatorname{Im}X_j$. All inverses are spectral Moore–Penrose inverses. Every positive-index matrix has split $n|n$. Set $L_j=A_j-\|C_j\|_{\mathrm{op}}I$ for $j\ge1$, where the norm is Euclidean induced. Separability always means the trace-norm closed convex hull of full oscillator product densities, independently of covariance witness inequalities.
--
--   Let $U,V$ be physical local CMs satisfying $\gamma_0\succeq U\oplus V$. Assume $\epsilon>0$ and $U\succeq iJ+\epsilon I$. Writing $\|A\|_{\mathrm{tr}}=\operatorname{tr}\sqrt{A^\dagger A}$, there exists an integer $N\ge1$ such that
--
--   $$
--   N<\frac{\|A_0\|_{\mathrm{tr}}-2n}{\epsilon}+1,\qquad L_N\succeq iJ.
--   $$
--
--   The strict cutoff is a real number, with the displayed $+1$ retained. This is a finite stopping guarantee for the stated local margin, not for every separable boundary covariance.
-- source:
--   Separability Criterion for all bipartite Gaussian States, arXiv:quant-ph/0104050v1, PDF p. 3, Proposition 3, Eq.(8)

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

/-- PDF p.3, Proposition 3: epsilon is positive as in the preceding paragraph.
The stopping index is N=k+1; the strict real bound and +1 in (8) are retained,
without rounding. Condition (6) is >=iJ, not the proof's >=0 typo. -/
theorem strictMarginFiniteStopping {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (g : CovarianceBlocks n m) (hg : IsPhysicalCovariance g) (U : Cov n) (V : Cov m)
    (hU : IsCM U) (hV : IsCM V) (hdom : DominatesLocalCovariances g U V)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hmargin : (complexify U - Complex.I • complexify (interleavedJ n) -
      (epsilon : ℂ) • (1 : Matrix (QuadratureIndex n) (QuadratureIndex n) ℂ)).PosSemidef) :
    ∃ k : ℕ, ((k + 1 : ℕ) : ℝ) <
      (QAlgorithms.traceNorm (complexify g.A) - 2 * (n : ℝ)) / epsilon + 1 ∧
      Uncertainty (lowerWitness (tail g k)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P68

end
