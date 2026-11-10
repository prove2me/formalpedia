-- Prove2me | Theorems.Thm_SYKFastMix_FastMixing_lemma_12
-- name    : SYKFastMix.FastMixing.lemma_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T14:08:06.329592+00:00
-- url     : https://prove2.me/theorems/b1e4651c-ca48-480d-a5f2-614617da756e
-- title:
--   Lemma 12 — block-superoperator versus classical coefficient moments
-- statement:
--   Let $N\ge4$ be even, $J>0$, $d=2^{N/2}$, and let $\gamma_1,\ldots,\gamma_N$ be any Hermitian CAR family on $\mathbb C^d$. The couplings are independent $\mathcal N(0,6J^2/N^3)$ variables and $H=\sum_{|A|=4}J_A\gamma_A$, using raw ordered quartic products. All traces are unnormalized and all operator norms are induced by Euclidean or Hilbert–Schmidt norms.
--
--   Let $m\ge0$ be an integer and $M_m=[s^m]M(\gamma(s),\gamma(-s))$. For every integer $p\ge1$, the trace moments are integrable and
--   $$\frac1{d^2}\mathbb E_J\operatorname{Tr}[(M_m^\dagger M_m)^p]\le(m+1)^{2p}\mathbb E_J\operatorname{Tr}[(\widetilde F_{m+1}(1)^\dagger\widetilde F_{m+1}(1))^p].$$
--   The first trace is on $\mathbb C^N\otimes\mathcal B(\mathcal H)$, of dimension $Nd^2$, and the second on $\mathbb C^N$. This extends coefficient comparison to the block operator controlling filtering.
--
--   Differences from the source:
--   - encoding: one-based sites on a complex Hilbert space with unnormalized traces → zero-based finite matrix coordinates, full operator spaces, and real parts of Hermitian quadratic forms; reason: an orthonormal basis identifies every source representation with these matrices; real parts do not change the real quadratic forms
--   - encoding: finite Gaussian-disorder moments → the moment integrands are explicitly asserted Integrable as part of the conclusion; reason: this records well-defined expectations and prevents the nonintegrable Bochner default from satisfying the bound
-- source:
--   Yiyi Cai, Yongtao Zhan, Alexander Zlokapa, Fast mixing of the SYK model at high temperatures, STOC 2027 submission #1050 (October 2026), p. 26, Lemma 12, Eq. (5.19)

import Mathlib
import Definitions.Def_SYKFastMix_FastMixing_Coefficients
import Definitions.Def_SYKFastMix_FastMixing_CompactGaussian

noncomputable section
open scoped Matrix.Norms.L2Operator
open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ComplexOrder

namespace SYKFastMix.FastMixing

theorem lemma_12 {N : ℕ} (Q : Model N) (m p : ℕ) (hp : 1 ≤ p) :
  Integrable (fun w => traceMoment p (mCoefficient Q w m)) (disorderLaw Q) ∧
  Integrable (fun w => traceMoment p (classicalCoefficient w (m+1) (fun _ => 1))) (disorderLaw Q) ∧
  (1 / ((2 ^ (N / 2) : ℝ)^2)) * (∫ w, traceMoment p (mCoefficient Q w m) ∂disorderLaw Q) ≤
    ((m : ℝ)+1)^(2*p) * (∫ w, traceMoment p (classicalCoefficient w (m+1) (fun _ => 1)) ∂disorderLaw Q) := by sorry

end SYKFastMix.FastMixing
