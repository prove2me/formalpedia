-- Prove2me | Theorems.Thm_SingleCopyMoments_Adaptive_log_derivative
-- name    : SingleCopyMoments.Adaptive.log_derivative
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T09:50:05.565108+00:00
-- url     : https://prove2.me/theorems/1fb8af4d-dd19-46e3-be23-c54d298aecba
-- title:
--   Lemma 40 — Expansion of the logarithmic derivative
-- statement:
--   Fix $r\ge2$ and $0<\alpha\le1/100$, and suppose $T(d)\log(d+T(d)+1)=o(d)$. Eventually, uniformly over every complete original rank-one record $H$ of length $T(d)$ and every interpolation parameter,
--
--   $$\partial_\theta\log p_\theta(H)=\mathbb E_\theta\left[\left.\sum_{\ell=r}^{T(d)}\frac{\alpha^\ell p'_\ell(\lambda(\theta))}{\ell}\widehat C_{\ell,T(d)}\ \right|\ H\right]+e_\theta(H),\qquad|e_\theta(H)|\le e^{-c_rd}.$$
--
--   The density is positive, the derivative exists, the physical posterior is a probability measure, and the summed complex integrand is integrable. The error is real; the equality is written in the complex numbers to retain complex chain traces. The posterior averages over the latent vectors with the complete observed projectors fixed. Cycles use the raw matrices $\widehat Y_i$, so the identity is not confined to good records.
--
--   This identifies the full likelihood derivative, including every surviving degree through $T(d)$.
--
--   Differences from the source:
--   - encoding: finite-dimensional states, measurable experiments, and their expectations → complex Fin d matrices, explicit Born/product measures, and normalized measurable operations; reason: the coordinate and measure conventions preserve every positive dimension and arbitrary rank; probability and integrability assertions are conclusions, not extra premises
--   - encoding: conditional expectation given each complete original record → the explicit normalized physical latent posterior with frozen projectors, and equality in complex scalars with a real remainder; reason: this preserves raw complex traces and every term of the sum without replacing the posterior by a Gaussian expectation
--   - encoding: the fixed sufficiently small prior parameter → 0<alpha<=1/100 from the prior construction; reason: the expansion and barrier replacement precede and do not require the later tail choice (7.44)
-- source:
--   Zhenhuan Liu, STOC 2027 submission #41 (October 2026), Lemma 40, (7.40), printed p. 45 (PDF p. 47); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/41.pdf; PDF SHA-256 f19fd65f41a444a79243fa55aab5dfca3db6adb571b06acff78ee49932174fa9.

import Definitions.Def_SingleCopyMoments_Adaptive_Records

open MeasureTheory
open scoped Matrix.Norms.L2Operator

namespace SingleCopyMoments.Adaptive

/-- Lemma 40, printed pp.45–46 (PDF pp.47–48). The posterior averages the
raw cycles over latent vectors with the observed projectors fixed. -/
theorem log_derivative (r : ℕ) (hr : 2 ≤ r) (α : ℝ) (hα : 0 < α)
    (hα₁ : α ≤ 1/100) (T : ℕ → ℕ) (hT : SublinearBudget T) :
    ∃ c > 0, ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → 0 < d →
      ∀ H : FrozenHistory d (T d), Frozen H → ∀ θ ∈ Set.Icc (0 : ℝ) (Real.pi/r),
        0 < recordDensity r α θ H ∧ IsProbabilityMeasure (posterior r α θ H) ∧
        DifferentiableAt ℝ (fun u => Real.log (recordDensity r α u H)) θ ∧
        Integrable (fun g => ∑ ℓ ∈ Finset.Icc r (T d),
          ((α^ℓ * deriv (spectralMoment r ℓ) θ / (ℓ : ℝ) : ℝ) : ℂ) * rawCycle α θ H ℓ g)
            (posterior r α θ H) ∧
        ∃ e : ℝ, |e| ≤ Real.exp (-c*d) ∧
          (deriv (fun u => Real.log (recordDensity r α u H)) θ : ℂ) =
            (∫ g, ∑ ℓ ∈ Finset.Icc r (T d),
              ((α^ℓ * deriv (spectralMoment r ℓ) θ / (ℓ : ℝ) : ℝ) : ℂ) *
                rawCycle α θ H ℓ g ∂posterior r α θ H) + (e : ℂ) := by sorry

end SingleCopyMoments.Adaptive
