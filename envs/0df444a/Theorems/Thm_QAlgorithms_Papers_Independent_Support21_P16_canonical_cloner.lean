-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P16_canonical_cloner
-- name    : QAlgorithms.Papers.Independent.Support21.P16.canonical_cloner
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T04:39:26.845598+00:00
-- url     : https://prove2.me/theorems/f1f35656-f6e5-48db-aa57-6a441145c202
-- title:
--   The canonical map is a covariant Bose-input channel
-- statement:
--   Let $d>0$ and $1\le N<M$ be integers. In the tensor powers of $H=\mathbb C^d$, let $s_k$ project onto the Bose subspace, write $D_k=\binom{d+k-1}{k}$, and set $\tau_k=s_k/D_k$. Define the zero-extended map
--   $$
--   \widehat T_{MN}(A)=\frac{D_N}{D_M}\,s_M\bigl((s_NAs_N)\otimes I^{\otimes(M-N)}\bigr)s_M.
--   $$
--   It is complex-linear and completely positive, obeys $\operatorname{tr}\widehat T_{MN}(A)=\operatorname{tr}(s_NAs_N)$, and has Bose-supported output for every ambient operator $A$. For every $U\in U(d)$ it satisfies
--   $$
--   \widehat T_{MN}(U^{\otimes N}AU^{*\otimes N})
--   =U^{\otimes M}\widehat T_{MN}(A)U^{*\otimes M},
--   \qquad \widehat T_{MN}(\tau_N)=\tau_M.
--   $$
--   This constructs a genuine trace-preserving channel on the effective Bose input algebra together with its covariance and invariant-state transport.
-- source:
--   Optimal Cloning of Pure States, arXiv:quant-ph/9804001v1, PDF p. 6, canonical-cloner

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P16

noncomputable section

open scoped Matrix ComplexOrder

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Support21.P16

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

open QAlgorithms.Papers.Independent.Renew46.P45
  (TensorMat boseProjector powerVector IsCloningCovariant haarAverage)

attribute [local instance] QAlgorithms.Papers.Independent.Support21.P16.unitaryMeasurable

/-- PDF p.6 Eqs.(3.3)–(3.4): the computed map is a corner-input CP TP channel,
with Bose output, covariance and tau transport. The prose's N-M blank count
is corrected to M-N, as in the displayed formula and factor indices. -/
theorem canonical_cloner (d N M : ℕ) (hd : 0 < d) (hN : 1 ≤ N) (hNM : N < M) :
    IsBoseInputChannel (canonicalCloner (d := d) hNM.le) ∧
    HasBoseOutput (canonicalCloner (d := d) hNM.le) ∧
    IsCloningCovariant (canonicalCloner (d := d) hNM.le) ∧
    canonicalCloner hNM.le (boseMixed d N) = boseMixed d M := by sorry

end QAlgorithms.Papers.Independent.Support21.P16

end
