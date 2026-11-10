-- Prove2me | Theorems.Thm_SYKFastMix_FastMixing_corollary_11
-- name    : SYKFastMix.FastMixing.corollary_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T14:08:18.531942+00:00
-- url     : https://prove2.me/theorems/89bb567b-6741-490a-93c7-5965f5a56ca9
-- title:
--   Corollary 11 — fermionic Jacobian coefficient moments
-- statement:
--   Let $N\ge4$ be even, $J>0$, $d=2^{N/2}$, and let $\gamma_1,\ldots,\gamma_N$ be any Hermitian CAR family on $\mathbb C^d$. The couplings are independent $\mathcal N(0,6J^2/N^3)$ variables and $H=\sum_{|A|=4}J_A\gamma_A$, using raw ordered quartic products. All traces are unnormalized and all operator norms are induced by Euclidean or Hilbert–Schmidt norms.
--
--   For integers $m,p\ge1$ with $mp\le7N$, the fermionic coefficients $F_m$ from (5.8) have integrable norm moments satisfying
--   $$\mathbb E_J\|F_m\|^{2p}\le Nd(105J)^{2pm}.$$
--   Here $F_m$ acts on the full $Nd$-dimensional block space. The dimension factor is retained for the later high-probability estimate.
--
--   Differences from the source:
--   - encoding: one-based sites on a complex Hilbert space with unnormalized traces → zero-based finite matrix coordinates, full operator spaces, and real parts of Hermitian quadratic forms; reason: an orthonormal basis identifies every source representation with these matrices; real parts do not change the real quadratic forms
--   - encoding: finite Gaussian-disorder moments → the moment integrands are explicitly asserted Integrable as part of the conclusion; reason: this records well-defined expectations and prevents the nonintegrable Bochner default from satisfying the bound
-- source:
--   Yiyi Cai, Yongtao Zhan, Alexander Zlokapa, Fast mixing of the SYK model at high temperatures, STOC 2027 submission #1050 (October 2026), p. 25, Corollary 11, Eq. (5.15)

import Mathlib
import Definitions.Def_SYKFastMix_FastMixing_Coefficients
import Definitions.Def_SYKFastMix_FastMixing_CompactGaussian

noncomputable section
open scoped Matrix.Norms.L2Operator
open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ComplexOrder

namespace SYKFastMix.FastMixing

theorem corollary_11 {N : ℕ} (Q : Model N) (m p : ℕ) (hm : 1 ≤ m) (hp : 1 ≤ p) (hmp : m * p ≤ 7 * N) :
  Integrable (fun w => SYKEdge.opNorm (fermionCoefficient Q w m)^(2*p)) (disorderLaw Q) ∧
  (∫ w, SYKEdge.opNorm (fermionCoefficient Q w m)^(2*p) ∂disorderLaw Q) ≤
    (N : ℝ) * 2^(N/2) * (105 * Q.J)^(2*p*m) := by sorry

end SYKFastMix.FastMixing
