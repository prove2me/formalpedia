-- Prove2me | Theorems.Thm_SYKFastMix_FastMixing_lemma_2
-- name    : SYKFastMix.FastMixing.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T14:07:50.543727+00:00
-- url     : https://prove2.me/theorems/3d1660d2-93ac-43ff-a239-e4c14d52ddd0
-- title:
--   Lemma 2 — discriminant as a sech-weighted average
-- statement:
--   Let $N\ge4$ be even, $J>0$, $d=2^{N/2}$, and let $\gamma_1,\ldots,\gamma_N$ be any Hermitian CAR family on $\mathbb C^d$. The couplings are independent $\mathcal N(0,6J^2/N^3)$ variables and $H=\sum_{|A|=4}J_A\gamma_A$, using raw ordered quartic products. All traces are unnormalized and all operator norms are induced by Euclidean or Hilbert–Schmidt norms.
--
--   Fix an arbitrary real disorder realization and $\beta>0$. The actual discriminant $D$ and filtered pseudo-Lindbladian $K_f$ satisfy
--   $$D=2\int_{\mathbb R}\frac2\beta\operatorname{sech}(2\pi s/\beta)\,e^{\mathrm i s\operatorname{ad}_H}K_fe^{-\mathrm i s\operatorname{ad}_H}\,ds.$$
--   Here $e^{\mathrm i s\operatorname{ad}_H}(X)=e^{\mathrm i sH}Xe^{-\mathrm i sH}$. The operator-valued integrand is integrable. This identity relates the computed Gibbs sampler to the auxiliary quadratic form.
--
--   Differences from the source:
--   - encoding: one-based sites on a complex Hilbert space with unnormalized traces → zero-based finite matrix coordinates, full operator spaces, and real parts of Hermitian quadratic forms; reason: an orthonormal basis identifies every source representation with these matrices; real parts do not change the real quadratic forms
--   - encoding: an integral identity over Hilbert–Schmidt linear operators → the finite-dimensional matrix-valued integrand is explicitly Integrable; reason: all finite-dimensional norms give the same Bochner integral and the source integral is convergent
-- source:
--   Yiyi Cai, Yongtao Zhan, Alexander Zlokapa, Fast mixing of the SYK model at high temperatures, STOC 2027 submission #1050 (October 2026), p. 14, Lemma 2, Eq. (3.11)

import Mathlib
import Definitions.Def_SYKFastMix_FastMixing_Coefficients
import Definitions.Def_SYKFastMix_FastMixing_CompactGaussian

noncomputable section
open scoped Matrix.Norms.L2Operator
open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ComplexOrder

namespace SYKFastMix.FastMixing

theorem lemma_2 {N : ℕ} (Q : Model N) (w : Disorder N) (β : ℝ) (hβ : 0 < β) :
  let H := hamiltonian Q w
  let F := fun s : ℝ => ((2 / β / Real.cosh (2 * Real.pi * s / β) : ℝ) : ℂ) •
    (mexp ((Complex.I * (s : ℂ)) • ad H) * filteredK Q w β *
      mexp ((-Complex.I * (s : ℂ)) • ad H))
  Integrable F ∧ discriminant H Q.γ β = (2 : ℂ) • (∫ s : ℝ, F s) := by sorry

end SYKFastMix.FastMixing
