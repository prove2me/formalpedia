-- Prove2me | Theorems.Thm_SpikedWishart_SoftEdge_kernelKMN_factorization
-- name    : SpikedWishart.SoftEdge.kernelKMN_factorization
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-04T09:04:48.490172+00:00
-- url     : https://prove2.me/theorems/6d6555d7-a0c5-4cf7-88be-26aa45923ba6
-- title:
--   Rescaled finite-$N$ kernel $K_{M,N}$ factors as $\int_0^\infty \mathcal H(u+y)\mathcal J(v+y)\,dy$
-- statement:
--   Let $0<M$, $0<N$, $k\le r\le N$, $\gamma>0$ with $\gamma^2=M/N$, and put $\sigma=\nu(\gamma)M^{1/3}$, $\eta=\mu(\gamma)+\sigma u/M$, $\zeta=\mu(\gamma)+\sigma v/M$. Let $\pi_1,\dots,\pi_N$ be real with $\pi_j=1$ for $j>r$, $\pi'_j=\pi_j$ for $j\le r$ and $\pi'_j=p_c$ for $j\le k$. Let $\Gamma$ (centre $c_\Gamma$, radius $\rho_\Gamma\ge0$) and $\Sigma$ (centre $c_\Sigma$, radius $\rho_\Sigma\ge0$) be counterclockwise circles with $c_\Sigma+\rho_\Sigma<c_\Gamma-\rho_\Gamma$, $\Gamma$ avoiding $0,1,\pi_j$ and $\Sigma$ avoiding $0,1$. Then, with $K_{M,N}$ the kernel (62) and $\mathcal H,\mathcal J$ defined by (103)-(104),
--
--   $$\frac{\sigma}{M}\,K_{M,N}(\eta,\zeta)=\mathrm{Re}\int_0^\infty\mathcal H(u+y)\,\mathcal J(v+y)\,dy ,$$
--
--   and $\mathcal H$, $\mathcal J$ are continuous functions on $\mathbb R$.
--
--   Role: this is the change of variables of Section 3.1 that rewrites the rescaled kernel of Proposition 2.1 as a product kernel built from $\mathcal H$ and $\mathcal J$, the form to which Proposition 3.1 applies.
-- source:
--   J. Baik, G. Ben Arous and S. Peche, Phase transition of the largest eigenvalue for nonnull complex sample covariance matrices, Ann. Probab. 33 (2005), https://doi.org/10.1214/009117905000000233, Section 3.1, (62) and (101)-(105) with the factorization of the rescaled kernel into (103)-(104), pp. 1660-1661

import Mathlib
import Definitions.Def_SpikedWishart_SoftEdge_Kernels
open MeasureTheory

namespace SpikedWishart.SoftEdge

theorem kernelKMN_factorization {N r : ℕ} (k M : ℕ) (hM : 0 < M) (hN : 0 < N) (hr : r ≤ N) (hkr : k ≤ r)
    (γ q cΓ ρΓ cS ρS u v η ζ : ℝ) (hγ : γ ^ 2 = (M : ℝ) / N) (hγ0 : 0 < γ)
    (hη : η * (M : ℝ) = mu γ * M + nu γ * (M : ℝ) ^ (1 / 3 : ℝ) * u)
    (hζ : ζ * (M : ℝ) = mu γ * M + nu γ * (M : ℝ) ^ (1 / 3 : ℝ) * v)
    (π : Fin N → ℝ) (π' : Fin r → ℝ) (hπ' : ∀ j : Fin r, π' j = π ⟨j, lt_of_lt_of_le j.2 hr⟩)
    (h1 : ∀ j : Fin N, r ≤ (j : ℕ) → π j = 1) (hpc : ∀ j : Fin r, (j : ℕ) < k → π' j = pc γ)
    (hρΓ : 0 ≤ ρΓ) (hρS : 0 ≤ ρS) (hsep : cS + ρS < cΓ - ρΓ)
    (hΓ : ∀ z ∈ Metric.sphere (cΓ : ℂ) ρΓ, z ≠ 0 ∧ 1 - z ≠ 0 ∧ ∀ j, (π j : ℂ) - z ≠ 0)
    (hSig : ∀ w ∈ Metric.sphere (cS : ℂ) ρS, w ≠ 0 ∧ 1 - w ≠ 0) :
    nu γ * (M : ℝ) ^ (1 / 3 : ℝ) / M * kernelKMN M π q cΓ ρΓ cS ρS η ζ =
      (∫ y in Set.Ioi (0 : ℝ), Hcal γ q M k π' cΓ ρΓ (u + y) * Jcal γ q M k π' cS ρS (v + y)).re ∧
    Continuous (Hcal γ q M k π' cΓ ρΓ) ∧ Continuous (Jcal γ q M k π' cS ρS) := by sorry

end SpikedWishart.SoftEdge
