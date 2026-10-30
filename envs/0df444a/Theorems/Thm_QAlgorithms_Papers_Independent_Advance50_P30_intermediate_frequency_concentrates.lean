-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P30_intermediate_frequency_concentrates
-- name    : QAlgorithms.Papers.Independent.Advance50.P30.intermediate_frequency_concentrates
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:55:32.556+00:00
-- url     : https://prove2.me/theorems/788c0075-8608-4bfb-8a63-86b7bd8d4b26
-- title:
--   Fact 1: concentration of every intermediate spectral estimate
-- statement:
--   Let $\mathcal H$ be a finite-dimensional complex Hilbert space of dimension $d\ge1$, with a fixed orthonormal basis. All states below are positive operators of trace one; pure states are unit vectors. Write $\|\cdot\|_1$ for the full trace norm (the full $\ell_1$ norm for classical distributions), $H_2$ for binary entropy in bits, and define
--   $$
--   e(\delta,N,r,w)=2^{-N[\delta^2/4-H_2(r/N)]+w\log_2(N/2+1)}.
--   $$
--
--   Use $t\ge1$ Hermitian, Hilbert–Schmidt orthonormal observables $L_i$ and arbitrary real coefficients $s_i$, and set $\Sigma=\sum_{i=1}^t s_iL_i$. For $m'\ge1$ let $m=tm'$. Measure each $L_i$ spectrally on its own block of $m'$ sites, and measure $\Sigma$ spectrally on a separate direct block. The indirect estimate is $I_m=\sum_i s_i\frac1{m'}\sum_{j=1}^{m'}\lambda_{i,j}$; the direct estimate $D_q=\frac1q\sum_{j=1}^q\gamma_j$ uses all $q$ sites in its block. All probabilities are the joint Born law of this tensor measurement, including its stated marginals.
--
--   Let $\sigma$ be a single-site state, and suppose the joint $2m$-site state is mixed almost-power along $\sigma$, meaning a reference reduction of a convex mixture of pure almost-power states along a purification of $\sigma$. Assume $2r\le m'$ and $\delta>0$. For each intermediate observable, let $P_i$ be its spectral outcome distribution on $\sigma$ and let $Q_i$ be its empirical spectral distribution on its assigned block. Then, under the same joint experiment with $q=m$,
--   $$
--   \Pr\{\|P_i-Q_i\|_1\ge\delta\}\le e(\delta,m',r,d)\qquad(1\le i\le t).
--   $$
--
--   The spectral alphabet has at most $d$ outcomes. This estimate provides the marginal concentration needed for the indirect estimator and keeps the printed non-strict threshold.
-- source:
--   Unconditional privacy over channels which cannot convey quantum information, arXiv:quant-ph/0702077v1, PDF p. 19, Fact 1

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P30

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P30

open QAlgorithms MeasureTheory

open QAlgorithms.Papers.Independent.Gap48.P20 (Copies)

open QAlgorithms.Papers.Independent.Information100.P21 (Op Vec)

open QAlgorithms.Papers.Independent.Information100.P69 (permute)

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

attribute [local instance] Classical.decEq Classical.propDecidable

attribute [local instance] QAlgorithms.Papers.Independent.Advance50.P30.matrixContinuousENorm

attribute [local instance] QAlgorithms.Papers.Independent.Advance50.P30.matrixMeasurable

attribute [local instance] QAlgorithms.Papers.Independent.Advance50.P30.matrixBorel

attribute [local instance] QAlgorithms.Papers.Independent.Advance50.P30.vectorMeasurable

attribute [local instance] QAlgorithms.Papers.Independent.Advance50.P30.vectorBorel

/-- PDF p.19, Fact 1, Eqs.(21)--(22): each marginal of the specified joint
experiment. The ≥ version follows from the > Chernoff estimate by taking
thresholds up to delta; no estimate is assumed as a hypothesis.
Printed setup only requires r ≤ m; changed to 2*r ≤ mp because the
invoked Theorem 1(3) requires r ≤ half the measured block length. -/
theorem intermediate_frequency_concentrates {I : Type} [Fintype I] [DecidableEq I]
    [Nonempty I] (t mp r : ℕ) (ht : 0 < t) (hmp : 0 < mp) (hr : 2 * r ≤ mp)
    (D : HSDecomposition I t) (S : Spectral I) (hS : S.operator = D.operator)
    (sigma : DensityState I) (rho : Op (Copies I (t * mp + t * mp)))
    (halong : AlmostAlong sigma (t * mp + t * mp) r rho)
    (delta : ℝ) (hdelta : 0 < delta) (i : Fin t) :
    estimationEvent D S mp (t * mp) rho (fun out =>
      l1 (fun a => effectProb ((D.intermediate i).effect a) sigma.val)
        (empiricalFrequency (out.1 i)) ≥ delta) ≤
      chernoffError delta mp r (Fintype.card I) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P30

end
