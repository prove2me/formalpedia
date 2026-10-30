-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P30_invariant_direct_indirect_estimation
-- name    : QAlgorithms.Papers.Independent.Advance50.P30.invariant_direct_indirect_estimation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:57:26.521787+00:00
-- url     : https://prove2.me/theorems/c65a9eac-38d4-4207-8017-e4ddaaa1a0fb
-- title:
--   Theorem 3: direct versus indirect estimation on invariant states
-- statement:
--   Let $\mathcal H$ be a finite-dimensional complex Hilbert space of dimension $d\ge1$, with a fixed orthonormal basis. All states below are positive operators of trace one; pure states are unit vectors. Write $\|\cdot\|_1$ for the full trace norm (the full $\ell_1$ norm for classical distributions), $H_2$ for binary entropy in bits, and define
--   $$
--   e(\delta,N,r,w)=2^{-N[\delta^2/4-H_2(r/N)]+w\log_2(N/2+1)}.
--   $$
--
--   Use $t\ge1$ Hermitian, Hilbert–Schmidt orthonormal observables $L_i$ and arbitrary real coefficients $s_i$, and set $\Sigma=\sum_{i=1}^t s_iL_i$. For $m'\ge1$ let $m=tm'$. Measure each $L_i$ spectrally on its own block of $m'$ sites, and measure $\Sigma$ spectrally on a separate direct block. The indirect estimate is $I_m=\sum_i s_i\frac1{m'}\sum_{j=1}^{m'}\lambda_{i,j}$; the direct estimate $D_q=\frac1q\sum_{j=1}^q\gamma_j$ uses all $q$ sites in its block. All probabilities are the joint Born law of this tensor measurement, including its stated marginals.
--
--   Let $n\ge1$, $2r\le m'$, $\delta>0$, and let $\rho_{2m+n}$ be a normalized density operator invariant under every copy permutation. Use the direct block of size $q=m+n$, in the same tensor experiment as the indirect block. For $h=\|\Sigma\|_{\mathrm{HS}}>0$,
--   $$
--   \Pr_{\rho_{2m+n}}\{|I_m-D_{m+n}|>3\delta\}\le e_1+e_2+e_3,
--   $$
--   where
--   $$
--   e_1=2\exp\!\left[-\frac{n(r+1)}{2(2m+n)}+\frac{d^2}{2}\ln n\right],\qquad
--   e_2=(t+1)e\!\left(\frac{\delta}{h\sqrt t},m',r,d\right),\qquad
--   e_3=d\exp\!\left[-\frac{m\delta^2}{8dh^2}\right].
--   $$
--   When $h=0$, the deviation probability is zero. Neither an IID hypothesis nor pure symmetric support is required. This is the general comparison theorem underpinning indirect observable estimation on coherent, permutation-invariant inputs.
-- source:
--   Unconditional privacy over channels which cannot convey quantum information, arXiv:quant-ph/0702077v1, PDF p. 22, Theorem 3

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

/-- PDF pp.22--23, Theorem 3, Eqs.(33)--(36): general invariant mixed input.
The exponent in e1 includes +(d^2/2)*ln n. In proof Eq.(38), delta replaces
the printed 3*delta so the triangle step gives Eq.(33)'s 3*delta; the theorem
statement itself is unchanged. The zero observable is handled deterministically.
The printed setup r ≤ m is restricted to 2*r ≤ mp, as required by the
cited reduced-block Chernoff estimate. No other error constant changes. -/
theorem invariant_direct_indirect_estimation {I : Type} [Fintype I] [DecidableEq I]
    [Nonempty I] (t mp n r : ℕ) (ht : 0 < t) (hmp : 0 < mp) (hn : 0 < n)
    (hr : 2 * r ≤ mp) (D : HSDecomposition I t) (S : Spectral I)
    (hS : S.operator = D.operator)
    (rho : Op (Copies I (t * mp + (t * mp + n))))
    (hrho : IsDensityMatrix rho) (hinv : InvariantCopyState rho)
    (delta : ℝ) (hdelta : 0 < delta) :
    (frobNorm D.operator = 0 →
      estimationEvent D S mp (t * mp + n) rho
        (fun out => |indirectMean D out - directMean S out| > 3 * delta) = 0) ∧
    (0 < frobNorm D.operator →
      estimationEvent D S mp (t * mp + n) rho
        (fun out => |indirectMean D out - directMean S out| > 3 * delta) ≤
        deFinettiError (t * mp + t * mp) n r (Fintype.card I) +
        ((t : ℝ) + 1) * chernoffError
          (delta / (frobNorm D.operator * Real.sqrt t)) mp r (Fintype.card I) +
        samplingError delta (t * mp) (Fintype.card I) (frobNorm D.operator)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P30

end
