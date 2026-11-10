-- Prove2me | Theorems.Thm_SYKFastMix_FastMixing_corollary_6
-- name    : SYKFastMix.FastMixing.corollary_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T14:08:33.85235+00:00
-- url     : https://prove2.me/theorems/9a551a32-cf62-4e35-a5aa-aa9e01228313
-- title:
--   Corollary 6 — quadratic-form comparison and equality of kernels
-- statement:
--   Let $N\ge4$ be even, $J>0$, $d=2^{N/2}$, and let $\gamma_1,\ldots,\gamma_N$ be any Hermitian CAR family on $\mathbb C^d$. The couplings are independent $\mathcal N(0,6J^2/N^3)$ variables and $H=\sum_{|A|=4}J_A\gamma_A$, using raw ordered quartic products. All traces are unnormalized and all operator norms are induced by Euclidean or Hilbert–Schmidt norms.
--
--   Fix an arbitrary real disorder realization. If $0\le\beta J\le1/1000$ and $\|M(\widetilde\gamma,\widetilde\gamma^\dagger)\|\le150J$, then for every operator $X$,
--   $$\langle X,K_f(X)\rangle_{\rm HS}\ge(13/14)^2\langle X,K(X)\rangle_{\rm HS}.$$
--   Moreover,
--   $$\ker K_f=\ker K.$$
--   The inequality and the two-sided kernel equality are both retained. Together they allow the unfiltered gap to control the sampler without introducing extra zero modes.
--
--   Differences from the source:
--   - encoding: one-based sites on a complex Hilbert space with unnormalized traces → zero-based finite matrix coordinates, full operator spaces, and real parts of Hermitian quadratic forms; reason: an orthonormal basis identifies every source representation with these matrices; real parts do not change the real quadratic forms
-- source:
--   Yiyi Cai, Yongtao Zhan, Alexander Zlokapa, Fast mixing of the SYK model at high temperatures, STOC 2027 submission #1050 (October 2026), p. 20, Corollary 6, Eq. (3.69)

import Mathlib
import Definitions.Def_SYKFastMix_FastMixing_Coefficients
import Definitions.Def_SYKFastMix_FastMixing_CompactGaussian

noncomputable section
open scoped Matrix.Norms.L2Operator
open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ComplexOrder

namespace SYKFastMix.FastMixing

theorem corollary_6 {N : ℕ} (Q : Model N) (w : Disorder N) (β : ℝ)
    (hβ : 0 ≤ β * Q.J ∧ β * Q.J ≤ 1/1000)
    (hM : SYKEdge.opNorm (blockM Q w (β/4)) ≤ 150 * Q.J) :
  (∀ X, (13/14 : ℝ)^2 * qform (unfilteredK Q w β) X ≤ qform (filteredK Q w β) X) ∧
  (∀ X, applySuper (filteredK Q w β) X = 0 ↔ applySuper (unfilteredK Q w β) X = 0) := by sorry

end SYKFastMix.FastMixing
