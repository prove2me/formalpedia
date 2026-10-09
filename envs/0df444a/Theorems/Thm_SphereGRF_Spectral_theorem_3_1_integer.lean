-- Prove2me | Theorems.Thm_SphereGRF_Spectral_theorem_3_1_integer
-- name    : SphereGRF.Spectral.theorem_3_1_integer
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:39:50.460958+00:00
-- url     : https://prove2.me/theorems/d3daea17-bd50-45a3-9a7c-463199407b55
-- title:
--   Theorem 3.1 for $\eta = n \in \mathbb N_0$, pp. 11–12 — $u \in V^n(-1,1)$ iff $\sum u_\ell^2\frac{2\ell+1}{2}(1+\ell^{2n}) < \infty$, with equivalent norms
-- statement:
--   Let $n \in \mathbb N_0$. There are constants $c_1, c_2 > 0$, depending only on $n$, such that for every $u \in L^2(-1,1)$ with Fourier–Legendre coefficients $u_\ell = \int_{-1}^1 u P_\ell$:
--
--   1. $u \in V^n(-1,1)$ if and only if
--   $$
--   \sum_{\ell=0}^\infty u_\ell^2\,\frac{2\ell+1}{2}\,(1+\ell^{2n}) < +\infty;
--   $$
--   2. if $u \in V^n(-1,1)$, then
--   $$
--   c_1 \sum_{\ell=0}^\infty u_\ell^2\,\frac{2\ell+1}{2}\,(1+\ell^{2n}) \le \|u\|^2_{V^n(-1,1)} \le c_2 \sum_{\ell=0}^\infty u_\ell^2\,\frac{2\ell+1}{2}\,(1+\ell^{2n}).
--   $$
--
--   In other words $u \mapsto (u_\ell)_\ell$ is an isomorphism of $V^n(-1,1)$ onto the weighted sequence space $\ell_n = \ell^2\big((\tfrac{2\ell+1}{2}(1+\ell^{2n}))_\ell\big)$. This is the integer case of Theorem 3.1, proved first in the paper; the fractional case follows from it by interpolation.
--
--   **Formalization Note** $V^n(-1,1)$ is the closure of the smooth functions in the weighted norm and $\|u\|_{V^n(-1,1)}$ the norm of the closure, valued in $[0,+\infty]$; the weighted sum is taken in $[0,+\infty]$. The second formulation of the theorem through the kernel $k_I$ and its weak derivatives is not part of this statement.
-- source:
--   Lang, Schwab, Isotropic Gaussian random fields on the sphere, arXiv:1305.1170v3, Theorem 3.1, p. 11, at η = n ∈ ℕ₀; proof, second step, p. 12

import Mathlib
import Definitions.Def_SphereGRF_Spectral_WeightedSobolev
import Definitions.Def_SphereGRF_Spectral_FourierLegendre

open scoped ENNReal

namespace SphereGRF.Spectral

/-- Theorem 3.1 for `η = n ∈ ℕ₀` (second step of its proof, p. 12): `V^n(−1,1)` is isomorphic to
`ℓ_n`. For `u ∈ L²(−1,1)`: `u ∈ V^n(−1,1)` iff `Σ u_ℓ² (2ℓ+1)/2 (1 + ℓ^{2n}) < ∞`, and this sum
is an equivalent squared norm, with constants depending only on `n`. -/
theorem theorem_3_1_integer (n : ℕ) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ u : ℝ → ℝ, L2m11 u →
      (MemV n u ↔ specWeightSum (n : ℝ) u < ⊤) ∧
      (MemV n u →
        ENNReal.ofReal c₁ * specWeightSum (n : ℝ) u ≤ vNorm n u ^ 2 ∧
        vNorm n u ^ 2 ≤ ENNReal.ofReal c₂ * specWeightSum (n : ℝ) u) := by sorry

end SphereGRF.Spectral
