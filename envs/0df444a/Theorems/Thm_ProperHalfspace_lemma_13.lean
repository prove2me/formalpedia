-- Prove2me | Theorems.Thm_ProperHalfspace_lemma_13
-- name    : ProperHalfspace.lemma_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:04:09.677775+00:00
-- url     : https://prove2.me/theorems/65ce3abb-a00a-4317-99e8-ee583aa31358
-- title:
--   Lemma 13 — $\Gamma_\rho(\tilde f)$ in terms of $M_\rho(f)$
-- statement:
--   Let $\rho\in[0,1)$ and $f:\{\pm1\}^n\to[-1,1]$. Writing $\mathrm{diag}(M)$ for the diagonal matrix with the same diagonal as $M$,
--   $$\Gamma_\rho(\tilde f)=\frac{\rho}{(1-\rho)^2}\bigl(M_\rho(f)-\rho\,\mathrm{diag}(M_\rho(f))\bigr)\preceq\frac{\rho}{(1-\rho)^2}M_\rho(f).$$
--
--   Every direction significant for the Gaussian matrix $\Gamma_\rho(\tilde f)$ is therefore significant for the Boolean matrix $M_\rho(f)$, up to scaling.
--
--   Differences from the source: none.
-- source:
--   De, Mossel, Nadimpalli, Neeman, Efficient Proper Agnostic Learning of Halfspaces, arXiv:2611.02344 (Nov. 1, 2026), Lemma 13, (5), p.19

import Mathlib
import Definitions.Def_ProperHalfspace_Gaussian
import Definitions.Def_ProperHalfspace_InfluencePCA

namespace ProperHalfspace

/-- Lemma 13, (5), p.19. De, Mossel, Nadimpalli, Neeman, arXiv:2611.02344 (Nov. 1, 2026). For `ρ ∈ [0, 1)` and `f : {±1}ⁿ → [−1, 1]`,
`Γ_ρ(f̃) = (ρ/(1−ρ)²)(M_ρ(f) − ρ diag(M_ρ(f))) ⪯ (ρ/(1−ρ)²) M_ρ(f)`. -/
theorem lemma_13 {n : ℕ} (f : Cube n → ℝ) (hf : IsBoundedOne f) (ρ : ℝ) (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ < 1) :
    gammaMatrix ρ (mlExt f) =
        (ρ / (1 - ρ) ^ 2) • (pcaMatrix ρ f - ρ • Matrix.diagonal (fun i => pcaMatrix ρ f i i)) ∧
    ((ρ / (1 - ρ) ^ 2) • pcaMatrix ρ f - gammaMatrix ρ (mlExt f)).PosSemidef := by sorry

end ProperHalfspace
