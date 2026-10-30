-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P30_close_mixture_estimation
-- name    : QAlgorithms.Papers.Independent.Advance50.P30.close_mixture_estimation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:56:31.926962+00:00
-- url     : https://prove2.me/theorems/a37f3f17-28f9-478b-ab01-6cc871ec15e9
-- title:
--   Lemma 6: estimation on states close to almost-power mixtures
-- statement:
--   Let $\mathcal H$ be a finite-dimensional complex Hilbert space of dimension $d\ge1$, with a fixed orthonormal basis. All states below are positive operators of trace one; pure states are unit vectors. Write $\|\cdot\|_1$ for the full trace norm (the full $\ell_1$ norm for classical distributions), $H_2$ for binary entropy in bits, and define
--   $$
--   e(\delta,N,r,w)=2^{-N[\delta^2/4-H_2(r/N)]+w\log_2(N/2+1)}.
--   $$
--
--   Use $t\ge1$ Hermitian, Hilbert–Schmidt orthonormal observables $L_i$ and arbitrary real coefficients $s_i$, and set $\Sigma=\sum_{i=1}^t s_iL_i$. For $m'\ge1$ let $m=tm'$. Measure each $L_i$ spectrally on its own block of $m'$ sites, and measure $\Sigma$ spectrally on a separate direct block. The indirect estimate is $I_m=\sum_i s_i\frac1{m'}\sum_{j=1}^{m'}\lambda_{i,j}$; the direct estimate $D_q=\frac1q\sum_{j=1}^q\gamma_j$ uses all $q$ sites in its block. All probabilities are the joint Born law of this tensor measurement, including its stated marginals.
--
--   Assume $2r\le m'$, $\delta>0$, and $\epsilon\ge0$. Let $\mu$ be a probability measure on the single-site density operators, and let $\tau_\sigma$ be a measurable, integrable family of normalized $2m$-site mixed almost-power states along $\sigma$ (reference reductions of convex mixtures along unit purifications). Let $\rho_{2m}$ be any normalized state satisfying
--   $$
--   \left\|\rho_{2m}-\int\tau_\sigma\,d\mu(\sigma)\right\|_1\le\epsilon.
--   $$
--   For $q=m$ and $h=\|\Sigma\|_{\mathrm{HS}}>0$, the actual joint Born law obeys
--   $$
--   \Pr_{\rho_{2m}}\{|D_m-I_m|>2\delta\}
--   \le(t+1)e\!\left(\frac{\delta}{h\sqrt t},m',r,d\right)+\epsilon.
--   $$
--   When $h=0$, this deviation probability is zero. The state $\rho_{2m}$ need not be invariant. This transfers the terminal probability estimate to arbitrary states close in full trace norm, with the source's unchanged additive $\epsilon$.
-- source:
--   Unconditional privacy over channels which cannot convey quantum information, arXiv:quant-ph/0702077v1, PDF p. 21, Lemma 6

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

/-- PDF p.21, Lemma 6, Eq.(32): arbitrary trace-norm-close states, including
non-invariant ones. Full trace norm gives the source's +epsilon allowance.
The deterministic zero-observable case is retained without dividing by zero.
This is the terminal probability bound, not the false numerical chain (30).
Printed setup r ≤ m is restricted to 2*r ≤ mp, the domain of the
Chernoff estimate used in the source. The zero-norm branch makes the
otherwise divided-by-zero observable case explicit. -/
theorem close_mixture_estimation {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (t mp r : ℕ) (ht : 0 < t) (hmp : 0 < mp) (hr : 2 * r ≤ mp)
    (D : HSDecomposition I t) (S : Spectral I) (hS : S.operator = D.operator)
    (rho : Op (Copies I (t * mp + t * mp))) (hrho : IsDensityMatrix rho)
    (mu : Measure (DensityState I)) (hmu : IsProbabilityMeasure mu)
    (family : DensityState I → Op (Copies I (t * mp + t * mp)))
    (hfmeas : Measurable family) (hfint : Integrable family mu)
    (hfalong : ∀ sigma, AlmostAlong sigma (t * mp + t * mp) r (family sigma))
    (epsilon : ℝ) (heps : 0 ≤ epsilon)
    (hclose : traceNorm (rho - ∫ sigma, family sigma ∂mu) ≤ epsilon)
    (delta : ℝ) (hdelta : 0 < delta) :
    (frobNorm D.operator = 0 →
      estimationEvent D S mp (t * mp) rho
        (fun out => |directMean S out - indirectMean D out| > 2 * delta) = 0) ∧
    (0 < frobNorm D.operator →
      estimationEvent D S mp (t * mp) rho
        (fun out => |directMean S out - indirectMean D out| > 2 * delta) ≤
        ((t : ℝ) + 1) * chernoffError
          (delta / (frobNorm D.operator * Real.sqrt t)) mp r (Fintype.card I) + epsilon) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P30

end
