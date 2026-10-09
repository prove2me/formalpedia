-- Prove2me | Theorems.Thm_SphereGRF_Spectral_weight_equivalence
-- name    : SphereGRF.Spectral.weight_equivalence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:39:56.495128+00:00
-- url     : https://prove2.me/theorems/beb2d31b-499e-4da2-a9df-82dd0ca012bc
-- title:
--   Proof of Theorem 3.1, p. 12 — the Stein–Weiss weights $w_n^{1-\theta}w_{n+1}^\theta$ are equivalent to $\frac{2\ell+1}{2}(1+\ell^{2(n+\theta)})$
-- statement:
--   For $\eta \ge 0$ and $\ell \in \mathbb N_0$ write $w_\eta(\ell) = \frac{2\ell+1}{2}(1 + \ell^{2\eta})$. Let $n \in \mathbb N_0$ and $0 < \theta < 1$. Then there are constants $c_1, c_2 > 0$ such that for all $\ell \in \mathbb N_0$
--
--   $$
--   c_1\, w_{n+\theta}(\ell) \le w_n(\ell)^{1-\theta}\,w_{n+1}(\ell)^{\theta} \le c_2\, w_{n+\theta}(\ell),
--   $$
--
--   where $w_n(\ell)^{1-\theta}w_{n+1}(\ell)^\theta = \frac{2\ell+1}{2}(1+\ell^{2n})^{1-\theta}(1+\ell^{2(n+1)})^\theta$.
--
--   By the Stein–Weiss theorem, $w_n^{1-\theta}w_{n+1}^\theta$ are the weights of the interpolation space $(\ell_n, \ell_{n+1})_{\theta,2}$; this statement identifies that space with $\ell_{n+\theta}$.
--
--   **Formalization Note** All powers are real powers with $0^0 = 1$; the constants may depend on $n$ and $\theta$ and are chosen before $\ell$.
-- source:
--   Lang, Schwab, Isotropic Gaussian random fields on the sphere, arXiv:1305.1170v3, §3, proof of Theorem 3.1, p. 12, first display and the sentence 'It remains to show that this is equivalent to (2ℓ+1)/2 (1 + ℓ^{2η})'

import Mathlib
import Definitions.Def_SphereGRF_Spectral_FourierLegendre

namespace SphereGRF.Spectral

/-- Proof of Theorem 3.1, p. 12: for `n ∈ ℕ₀` and `θ ∈ (0,1)` the Stein–Weiss weights
`((2ℓ+1)/2 (1 + ℓ^{2n}))^{1−θ} ((2ℓ+1)/2 (1 + ℓ^{2(n+1)}))^θ` are equivalent to
`(2ℓ+1)/2 (1 + ℓ^{2(n+θ)})`, uniformly in `ℓ`. -/
theorem weight_equivalence (n : ℕ) (θ : ℝ) (hθ₀ : 0 < θ) (hθ₁ : θ < 1) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ ℓ : ℕ,
      c₁ * specWeight ((n : ℝ) + θ) ℓ ≤
        specWeight (n : ℝ) ℓ ^ (1 - θ) * specWeight ((n : ℝ) + 1) ℓ ^ θ ∧
      specWeight (n : ℝ) ℓ ^ (1 - θ) * specWeight ((n : ℝ) + 1) ℓ ^ θ ≤
        c₂ * specWeight ((n : ℝ) + θ) ℓ := by sorry

end SphereGRF.Spectral
