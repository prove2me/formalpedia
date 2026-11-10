-- Prove2me | Theorems.Thm_SYKFastMix_FastMixing_lemma_5
-- name    : SYKFastMix.FastMixing.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T14:08:02.364061+00:00
-- url     : https://prove2.me/theorems/414c3555-c2c4-4f18-81af-da830d1e5108
-- title:
--   Lemma 5 — filtering changes jump differences by at most one fourteenth
-- statement:
--   Let $N\ge4$ be even, $J>0$, $d=2^{N/2}$, and let $\gamma_1,\ldots,\gamma_N$ be any Hermitian CAR family on $\mathbb C^d$. The couplings are independent $\mathcal N(0,6J^2/N^3)$ variables and $H=\sum_{|A|=4}J_A\gamma_A$, using raw ordered quartic products. All traces are unnormalized and all operator norms are induced by Euclidean or Hilbert–Schmidt norms.
--
--   Fix an arbitrary real disorder realization. If $0\le\beta J\le1/1000$ and $\|M(\widetilde\gamma,\widetilde\gamma^\dagger)\|\le150J$, then every operator $X$ satisfies
--   $$\left(\sum_i\|c_i^f(X)-c_i(X)\|_2^2\right)^{1/2}\le\frac1{14}\left(\sum_i\|c_i(X)\|_2^2\right)^{1/2}.$$
--   Here $c_i^f(X)=(A_iX-XA_i^\dagger)/2$ uses the computed Gaussian-filtered jump. The endpoint $\beta=0$ is included. This relative estimate retains control even on the common kernel.
--
--   Differences from the source:
--   - encoding: one-based sites on a complex Hilbert space with unnormalized traces → zero-based finite matrix coordinates, full operator spaces, and real parts of Hermitian quadratic forms; reason: an orthonormal basis identifies every source representation with these matrices; real parts do not change the real quadratic forms
-- source:
--   Yiyi Cai, Yongtao Zhan, Alexander Zlokapa, Fast mixing of the SYK model at high temperatures, STOC 2027 submission #1050 (October 2026), p. 18, Lemma 5, Eq. (3.50)

import Mathlib
import Definitions.Def_SYKFastMix_FastMixing_Coefficients
import Definitions.Def_SYKFastMix_FastMixing_CompactGaussian

noncomputable section
open scoped Matrix.Norms.L2Operator
open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ComplexOrder

namespace SYKFastMix.FastMixing

theorem lemma_5 {N : ℕ} (Q : Model N) (w : Disorder N) (β : ℝ)
    (hβ : 0 ≤ β * Q.J ∧ β * Q.J ≤ 1/1000)
    (hM : SYKEdge.opNorm (blockM Q w (β/4)) ≤ 150 * Q.J) :
  ∀ X, Real.sqrt (∑ i, hsSq (applySuper (cfMap Q w β i) X - applySuper (cMap Q w β i) X)) ≤
    (1/14 : ℝ) * Real.sqrt (∑ i, hsSq (applySuper (cMap Q w β i) X)) := by sorry

end SYKFastMix.FastMixing
