-- Prove2me | Theorems.Thm_SYKFastMix_FastMixing_corollary_13
-- name    : SYKFastMix.FastMixing.corollary_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T14:08:00.122221+00:00
-- url     : https://prove2.me/theorems/038e6e58-ebbe-47a9-ab96-4b1bd293c64c
-- title:
--   Corollary 13 — block Taylor coefficient norm moments
-- statement:
--   Let $N\ge4$ be even, $J>0$, $d=2^{N/2}$, and let $\gamma_1,\ldots,\gamma_N$ be any Hermitian CAR family on $\mathbb C^d$. The couplings are independent $\mathcal N(0,6J^2/N^3)$ variables and $H=\sum_{|A|=4}J_A\gamma_A$, using raw ordered quartic products. All traces are unnormalized and all operator norms are induced by Euclidean or Hilbert–Schmidt norms.
--
--   For integers $m\ge0$, $p\ge1$, with $(m+1)p\le7N$, the coefficients $M_m$ have integrable norm moments and satisfy
--   $$\mathbb E_J\|M_m\|^{2p}\le Nd^2(m+1)^{2p}(105J)^{2p(m+1)}.$$
--   The norm is induced by $\sum_i\|X_i\|_2^2$ on $N$ copies of operator space. This bound retains the coefficient order, the zero-order case, and the full dimension factor.
--
--   Differences from the source:
--   - encoding: one-based sites on a complex Hilbert space with unnormalized traces → zero-based finite matrix coordinates, full operator spaces, and real parts of Hermitian quadratic forms; reason: an orthonormal basis identifies every source representation with these matrices; real parts do not change the real quadratic forms
--   - encoding: finite Gaussian-disorder moments → the moment integrands are explicitly asserted Integrable as part of the conclusion; reason: this records well-defined expectations and prevents the nonintegrable Bochner default from satisfying the bound
-- source:
--   Yiyi Cai, Yongtao Zhan, Alexander Zlokapa, Fast mixing of the SYK model at high temperatures, STOC 2027 submission #1050 (October 2026), p. 27, Corollary 13, Eq. (5.26)

import Mathlib
import Definitions.Def_SYKFastMix_FastMixing_Coefficients
import Definitions.Def_SYKFastMix_FastMixing_CompactGaussian

noncomputable section
open scoped Matrix.Norms.L2Operator
open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ComplexOrder

namespace SYKFastMix.FastMixing

theorem corollary_13 {N : ℕ} (Q : Model N) (m p : ℕ) (hp : 1 ≤ p) (hmp : (m+1)*p ≤ 7*N) :
  Integrable (fun w => SYKEdge.opNorm (mCoefficient Q w m)^(2*p)) (disorderLaw Q) ∧
  (∫ w, SYKEdge.opNorm (mCoefficient Q w m)^(2*p) ∂disorderLaw Q) ≤
    (N : ℝ) * (2^(N/2) : ℝ)^2 * ((m : ℝ)+1)^(2*p) * (105 * Q.J)^(2*p*(m+1)) := by sorry

end SYKFastMix.FastMixing
