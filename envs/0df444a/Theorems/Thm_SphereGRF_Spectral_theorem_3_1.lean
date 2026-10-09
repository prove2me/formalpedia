-- Prove2me | Theorems.Thm_SphereGRF_Spectral_theorem_3_1
-- name    : SphereGRF.Spectral.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:39:56.093607+00:00
-- url     : https://prove2.me/theorems/3e963893-d092-4070-b460-6d156e79cda4
-- title:
--   Theorem 3.1, p. 11 — $u \in V^\eta(-1,1)$ iff $\sum u_\ell^2\frac{2\ell+1}{2}(1+\ell^{2\eta}) < \infty$, an equivalent norm on $V^\eta(-1,1)$
-- statement:
--   Let $\eta \ge 0$. There are constants $c_1, c_2 > 0$, depending only on $\eta$, such that for every $u \in L^2(-1,1)$ with Fourier–Legendre coefficients $u_\ell = \int_{-1}^1 u(x)P_\ell(x)\,dx$:
--
--   1. $u \in V^\eta(-1,1)$ if and only if
--   $$
--   \sum_{\ell=0}^\infty u_\ell^2\,\frac{2\ell+1}{2}\,(1+\ell^{2\eta}) < +\infty;
--   $$
--   2. if $u \in V^\eta(-1,1)$, then
--   $$
--   c_1 \sum_{\ell=0}^\infty u_\ell^2\,\frac{2\ell+1}{2}\,(1+\ell^{2\eta}) \le \|u\|^2_{V^\eta(-1,1)} \le c_2 \sum_{\ell=0}^\infty u_\ell^2\,\frac{2\ell+1}{2}\,(1+\ell^{2\eta}),
--   $$
--   that is, the weighted sum is an equivalent squared norm on $V^\eta(-1,1)$.
--
--   Here $V^\eta(-1,1)$ is the weighted Sobolev space $V^n(-1,1)$ for $\eta = n \in \mathbb N_0$, and the real interpolation space $(V^n(-1,1), V^{n+1}(-1,1))_{\eta-n,2}$ with its K-functional norm for $n < \eta < n+1$. Applied to an isotropic covariance kernel $k_I = \sum_\ell A_\ell \frac{2\ell+1}{4\pi} P_\ell$ ($A_\ell = 2\pi u_\ell$), the theorem says that the regularity of the kernel is equivalent to weighted square summability of the angular power spectrum $(A_\ell)$.
--
--   **Formalization Note** The paper's $\eta \in \mathbb R_+$ is taken as $\eta \ge 0$ (at $\eta = 0$, $V^0(-1,1) = L^2(-1,1)$). Norms and sums take values in $[0,+\infty]$; $\ell^{2\eta}$ is the real power with $0^0 = 1$. The constants are chosen before $u$, as an equivalence of norms requires. The second paragraph of the paper's theorem (the formulation through $k_I$ and its weak derivatives) is the integer case restated and is not part of this statement.
-- source:
--   Lang, Schwab, Isotropic Gaussian random fields on the sphere, arXiv:1305.1170v3, Theorem 3.1, p. 11 (first statement)

import Mathlib
import Definitions.Def_SphereGRF_Spectral_WeightedSobolev
import Definitions.Def_SphereGRF_Spectral_FourierLegendre

open scoped ENNReal

namespace SphereGRF.Spectral

/-- Theorem 3.1, p. 11: for `η ≥ 0` there are constants `c₁, c₂ > 0` such that for every
`u ∈ L²(−1,1)`: `u ∈ V^η(−1,1)` iff `Σ u_ℓ² (2ℓ+1)/2 (1 + ℓ^{2η}) < ∞`, and then
`c₁ Σ ≤ ‖u‖²_{V^η(−1,1)} ≤ c₂ Σ`. -/
theorem theorem_3_1 (η : ℝ) (hη : 0 ≤ η) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ u : ℝ → ℝ, L2m11 u →
      (MemVeta η u ↔ specWeightSum η u < ⊤) ∧
      (MemVeta η u →
        ENNReal.ofReal c₁ * specWeightSum η u ≤ vEtaNormSq η u ∧
        vEtaNormSq η u ≤ ENNReal.ofReal c₂ * specWeightSum η u) := by sorry

end SphereGRF.Spectral
