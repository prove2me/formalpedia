-- Prove2me | Theorems.Thm_SYKFastMix_FastMixing_lemma_10
-- name    : SYKFastMix.FastMixing.lemma_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T14:08:02.772608+00:00
-- url     : https://prove2.me/theorems/95b880ab-93d5-4277-9891-340238bf7fc1
-- title:
--   Lemma 10 — classical Jacobian coefficient moments with constant 105
-- statement:
--   Let $N\ge4$ be even, $J>0$, $d=2^{N/2}$, and let $\gamma_1,\ldots,\gamma_N$ be any Hermitian CAR family on $\mathbb C^d$. The couplings are independent $\mathcal N(0,6J^2/N^3)$ variables and $H=\sum_{|A|=4}J_A\gamma_A$, using raw ordered quartic products. All traces are unnormalized and all operator norms are induced by Euclidean or Hilbert–Schmidt norms.
--
--   For integers $m,p\ge1$ with $mp\le7N$, let $\widetilde F_m(1)$ be the classical Jacobian coefficient from (5.8). Its norm moment is integrable and
--   $$\left(\mathbb E_J\|\widetilde F_m(1)\|^{2p}\right)^{1/(2p)}\le(105J)^m.$$
--   The derivative is taken on all of $\mathbb R^N$ before evaluation at the all-ones vector. This coefficient bound is uniform over all admissible sizes and orders.
--
--   Differences from the source:
--   - encoding: one-based sites on a complex Hilbert space with unnormalized traces → zero-based finite matrix coordinates, full operator spaces, and real parts of Hermitian quadratic forms; reason: an orthonormal basis identifies every source representation with these matrices; real parts do not change the real quadratic forms
--   - encoding: finite Gaussian-disorder moments → the moment integrands are explicitly asserted Integrable as part of the conclusion; reason: this records well-defined expectations and prevents the nonintegrable Bochner default from satisfying the bound
-- source:
--   Yiyi Cai, Yongtao Zhan, Alexander Zlokapa, Fast mixing of the SYK model at high temperatures, STOC 2027 submission #1050 (October 2026), p. 25, Lemma 10, Eq. (5.14)

import Mathlib
import Definitions.Def_SYKFastMix_FastMixing_Coefficients
import Definitions.Def_SYKFastMix_FastMixing_CompactGaussian

noncomputable section
open scoped Matrix.Norms.L2Operator
open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ComplexOrder

namespace SYKFastMix.FastMixing

theorem lemma_10 {N : ℕ} (Q : Model N) (m p : ℕ) (hm : 1 ≤ m) (hp : 1 ≤ p) (hmp : m * p ≤ 7 * N) :
  Integrable (fun w => SYKEdge.opNorm (classicalCoefficient w m (fun _ => 1))^(2*p)) (disorderLaw Q) ∧
  Real.rpow (∫ w, SYKEdge.opNorm (classicalCoefficient w m (fun _ => 1))^(2*p) ∂disorderLaw Q)
    (1 / (2 * (p : ℝ))) ≤ (105 * Q.J)^m := by sorry

end SYKFastMix.FastMixing
