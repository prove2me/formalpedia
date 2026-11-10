-- Prove2me | Theorems.Thm_SYKFastMix_FastMixing_lemma_9
-- name    : SYKFastMix.FastMixing.lemma_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T14:08:11.50843+00:00
-- url     : https://prove2.me/theorems/b5add0b4-b13c-4474-93c6-96d157b095e2
-- title:
--   Lemma 9 — quantum versus classical coefficient trace moments
-- statement:
--   Let $N\ge4$ be even, $J>0$, $d=2^{N/2}$, and let $\gamma_1,\ldots,\gamma_N$ be any Hermitian CAR family on $\mathbb C^d$. The couplings are independent $\mathcal N(0,6J^2/N^3)$ variables and $H=\sum_{|A|=4}J_A\gamma_A$, using raw ordered quartic products. All traces are unnormalized and all operator norms are induced by Euclidean or Hilbert–Schmidt norms.
--
--   For integers $m,p\ge1$, let $F_m$ and $\widetilde F_m(1)$ be the fermionic and classical coefficients of (5.8), evaluated at the all-ones vector in the latter case. Their trace moments are integrable and satisfy
--   $$\frac1d\mathbb E_J\operatorname{Tr}[(F_m^\dagger F_m)^p]\le\mathbb E_J\operatorname{Tr}[(\widetilde F_m(1)^\dagger\widetilde F_m(1))^p].$$
--   The first trace acts on $\mathbb C^N\otimes\mathbb C^d$ and the second on $\mathbb C^N$. This comparison transfers classical coefficient estimates to fermionic ones.
--
--   Differences from the source:
--   - encoding: one-based sites on a complex Hilbert space with unnormalized traces → zero-based finite matrix coordinates, full operator spaces, and real parts of Hermitian quadratic forms; reason: an orthonormal basis identifies every source representation with these matrices; real parts do not change the real quadratic forms
--   - encoding: finite Gaussian-disorder moments → the moment integrands are explicitly asserted Integrable as part of the conclusion; reason: this records well-defined expectations and prevents the nonintegrable Bochner default from satisfying the bound
-- source:
--   Yiyi Cai, Yongtao Zhan, Alexander Zlokapa, Fast mixing of the SYK model at high temperatures, STOC 2027 submission #1050 (October 2026), p. 25, Lemma 9, Eq. (5.9)

import Mathlib
import Definitions.Def_SYKFastMix_FastMixing_Coefficients
import Definitions.Def_SYKFastMix_FastMixing_CompactGaussian

noncomputable section
open scoped Matrix.Norms.L2Operator
open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ComplexOrder

namespace SYKFastMix.FastMixing

theorem lemma_9 {N : ℕ} (Q : Model N) (m p : ℕ) (hm : 1 ≤ m) (hp : 1 ≤ p) :
  Integrable (fun w => traceMoment p (fermionCoefficient Q w m)) (disorderLaw Q) ∧
  Integrable (fun w => traceMoment p (classicalCoefficient w m (fun _ => 1))) (disorderLaw Q) ∧
  (1 / (2 ^ (N / 2) : ℝ)) * (∫ w, traceMoment p (fermionCoefficient Q w m) ∂disorderLaw Q) ≤
    ∫ w, traceMoment p (classicalCoefficient w m (fun _ => 1)) ∂disorderLaw Q := by sorry

end SYKFastMix.FastMixing
