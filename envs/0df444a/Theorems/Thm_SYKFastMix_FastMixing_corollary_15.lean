-- Prove2me | Theorems.Thm_SYKFastMix_FastMixing_corollary_15
-- name    : SYKFastMix.FastMixing.corollary_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T14:08:05.029442+00:00
-- url     : https://prove2.me/theorems/df65f858-f7ca-4609-abee-08324d21b4ba
-- title:
--   Corollary 15 — one disorder event controls all allowed real times
-- statement:
--   Let $N\ge4$ be even, $J>0$, $d=2^{N/2}$, and let $\gamma_1,\ldots,\gamma_N$ be any Hermitian CAR family on $\mathbb C^d$. The couplings are independent $\mathcal N(0,6J^2/N^3)$ variables and $H=\sum_{|A|=4}J_A\gamma_A$, using raw ordered quartic products. All traces are unnormalized and all operator norms are induced by Euclidean or Hilbert–Schmidt norms.
--
--   There is a measurable disorder event of probability at least $1-2e^{-N}$ on which $\|H\|\le2JN$ and, simultaneously for every real $s$ satisfying $133J|s|<1$,
--   $$\|D\gamma(s)-I\|\le\frac{133J|s|}{1-133J|s|},\qquad \|M(\gamma(s),\gamma(-s))\|\le\frac{133J}{(1-133J|s|)^2}.$$
--   On that same domain the coefficient series sum to the actual Jacobian and block operator. The single continuous-time event supplies all temperatures needed in the main theorem.
--
--   Differences from the source:
--   - encoding: one-based sites on a complex Hilbert space with unnormalized traces → zero-based finite matrix coordinates, full operator spaces, and real parts of Hermitian quadratic forms; reason: an orthonormal basis identifies every source representation with these matrices; real parts do not change the real quadratic forms
--   - encoding: the simultaneous bounds obtained by summing (5.32) in (5.33)–(5.34) → a measurable event and both HasSum identities are explicit conclusions; reason: this records the source proof’s convergence of the actual operator series and does not assume a Taylor convergence domain
-- source:
--   Yiyi Cai, Yongtao Zhan, Alexander Zlokapa, Fast mixing of the SYK model at high temperatures, STOC 2027 submission #1050 (October 2026), p. 27, Corollary 15, Eq. (5.28); convergence in (5.32)–(5.34), p.28

import Mathlib
import Definitions.Def_SYKFastMix_FastMixing_Coefficients
import Definitions.Def_SYKFastMix_FastMixing_CompactGaussian

noncomputable section
open scoped Matrix.Norms.L2Operator
open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ComplexOrder

namespace SYKFastMix.FastMixing

theorem corollary_15 {N : ℕ} (Q : Model N) :
  ∃ A : Set (Disorder N), MeasurableSet A ∧
    ENNReal.ofReal (1 - 2 * Real.exp (-(N : ℝ))) ≤ disorderLaw Q A ∧
    ∀ w ∈ A, SYKEdge.opNorm (hamiltonian Q w) ≤ 2 * Q.J * N ∧
      ∀ s : ℝ, 133 * Q.J * |s| < 1 →
        SYKEdge.opNorm (jacobian Q w s - 1) ≤ 133 * Q.J * |s| / (1 - 133 * Q.J * |s|) ∧
        SYKEdge.opNorm (blockM Q w s) ≤ 133 * Q.J / (1 - 133 * Q.J * |s|)^2 ∧
        HasSum (fun m : ℕ => (s : ℂ)^m • fermionCoefficient Q w m) (jacobian Q w s) ∧
        HasSum (fun m : ℕ => (s : ℂ)^m • mCoefficient Q w m) (blockM Q w s) := by sorry

end SYKFastMix.FastMixing
