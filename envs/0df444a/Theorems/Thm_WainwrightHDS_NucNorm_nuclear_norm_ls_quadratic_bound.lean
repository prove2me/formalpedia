-- Prove2me | Theorems.Thm_WainwrightHDS_NucNorm_nuclear_norm_ls_quadratic_bound
-- name    : WainwrightHDS.NucNorm.nuclear_norm_ls_quadratic_bound
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-10-31T01:37:46.086971+00:00
-- url     : https://prove2.me/theorems/5e5ec736-8fe7-490f-a8d3-3e0b72da8d19
-- title:
--   Intermediate quadratic inequality in Proposition 10.6 for nuclear-norm regularized least squares
-- statement:
--   Under restricted strong convexity with curvature $\kappa > 0$ and constant $c_0 > 0$, on the dual-norm event $\|\frac{1}{n}\sum_{i=1}^n w_i X_i\|_2 \le \lambda_n/2$, every minimizer $\hat{\Theta}$ of the nuclear-norm regularized least-squares objective with $1 \le r \le \min(d_1, d_2)$ and $128 c_0 (d_1 + d_2) r \le \kappa n$ satisfies the quadratic inequality $\kappa \|\hat{\Theta} - \Theta^*\|_F^2 \le \frac{3}{2}\lambda_n\sqrt{2r}\,\|\hat{\Theta} - \Theta^*\|_F + \lambda_n \sum_{j=r+1}^{d'} \sigma_j(\Theta^*) + 16 c_0 \frac{d_1 + d_2}{n}\left(\sum_{j=r+1}^{d'} \sigma_j(\Theta^*)\right)^2$.

import Mathlib
import Definitions.Def_WainwrightHDS_NucNorm_obsOp
import Definitions.Def_WainwrightHDS_NucNorm_frobSq
import Definitions.Def_WainwrightHDS_NucNorm_nucNorm
import Definitions.Def_WainwrightHDS_NucNorm_opNorm2
import Definitions.Def_WainwrightHDS_NucNorm_lsNucObjective
import Definitions.Def_WainwrightHDS_NucNorm_singVal

namespace WainwrightHDS.NucNorm

/-- **Intermediate quadratic inequality in the proof of Proposition 10.6 (Wainwright §10.2.2, p. 320).**
Under restricted strong convexity (10.17) and the dual-norm event `|||(1/n) ∑ᵢ wᵢ Xᵢ|||₂ ≤ λₙ/2`,
choosing `(𝕌, 𝕍)` to be the top-`r` left and right singular subspaces of `Θ*` and combining the
nuclear-norm cone constraint (10.15) with `Ψ(𝕄̄(𝕌, 𝕍)) ≤ √(2r)` and `128 c₀ (d₁ + d₂) r ≤ κ n`
yields the quadratic inequality in `|||Θ̂ − Θ*|||_F`:
`κ |||Θ̂ − Θ*|||_F² ≤ (3/2) λₙ √(2r) |||Θ̂ − Θ*|||_F + λₙ ∑_{j=r+1}^{d'} σ_j(Θ*) + 16 c₀ ((d₁+d₂)/n) [∑_{j=r+1}^{d'} σ_j(Θ*)]²`. -/
theorem nuclear_norm_ls_quadratic_bound {n d₁ d₂ : ℕ}
    (X : Fin n → Matrix (Fin d₁) (Fin d₂) ℝ) (Θstar : Matrix (Fin d₁) (Fin d₂) ℝ)
    (w y : Fin n → ℝ) (hy : ∀ i, y i = obsOp X Θstar i + w i)
    (κ c₀ lam : ℝ) (hκ : 0 < κ) (hc₀ : 0 < c₀) (hlam : 0 < lam)
    (hRSC : ∀ Δ : Matrix (Fin d₁) (Fin d₂) ℝ,
      1 / (2 * (n : ℝ)) * ∑ i, (obsOp X Δ i) ^ 2 ≥
        κ / 2 * frobSq Δ - c₀ * (((d₁ : ℝ) + d₂) / n) * nucNorm Δ ^ 2)
    (hG : opNorm2 ((1 / (n : ℝ)) • ∑ i, w i • X i) ≤ lam / 2)
    (Θhat : Matrix (Fin d₁) (Fin d₂) ℝ)
    (hmin : ∀ Θ : Matrix (Fin d₁) (Fin d₂) ℝ, lsNucObjective X y lam Θhat ≤ lsNucObjective X y lam Θ)
    (r : ℕ) (hr₁ : 1 ≤ r) (hrd : r ≤ min d₁ d₂)
    (hrκ : 128 * c₀ * ((d₁ : ℝ) + d₂) * r ≤ κ * n) :
    κ * frobSq (Θhat - Θstar) ≤
      3 / 2 * lam * Real.sqrt (2 * r) * Real.sqrt (frobSq (Θhat - Θstar)) +
        lam * (∑ j ∈ Finset.Ico r (min d₁ d₂), singVal j Θstar) +
        16 * c₀ * ((d₁ : ℝ) + d₂) / n *
          (∑ j ∈ Finset.Ico r (min d₁ d₂), singVal j Θstar) ^ 2 := by sorry

end WainwrightHDS.NucNorm
