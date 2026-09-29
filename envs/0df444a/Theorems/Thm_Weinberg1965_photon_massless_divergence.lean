-- Prove2me | Theorems.Thm_Weinberg1965_photon_massless_divergence
-- name    : Weinberg1965.photon_massless_divergence
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T23:23:59.714794+00:00
-- url     : https://prove2.me/theorems/7942b271-f335-489a-9b01-4b7362fc38e7
-- title:
--   Eq. (3.3) — the soft-photon exponent diverges for a massless charged line
-- statement:
--   Let the external lines $n$ have three-momenta $\mathbf p_n$, charges $e_n$ and signs $\eta_n=\pm1$, with charge conservation $\sum_n\eta_ne_n=0$. Single out one line $1$ with $m_1=0$, $\mathbf p_1\ne\mathbf 0$ and nonzero charge $e_1\ne0$, all other lines being massive, $m_n>0$ for $n\ne1$. Let $A(\mu)$ denote the infrared-photon exponent (2.14) computed with the mass of line $1$ replaced by $\mu>0$. Then
--   $$A(\mu)\longrightarrow+\infty\qquad(\mu\to0^+).$$
--
--   This is Eq. (3.3): the divergent part of $A$ is $-\frac{e_1^2}{2\pi^2}\ln m_1$, so “quantum electrodynamics would be in serious trouble if any charged particle had zero mass” — in contrast with the gravitational cancellation of Eq. (3.5).
--
--   **Formalization Note** “$m_1\to0$ with $\mathbf p_1$ fixed” is encoded as the one-sided limit $\mu\to0^+$ with the mass of line $1$ set to $\mu$.
-- source:
--   S. Weinberg, Infrared Photons and Gravitons, Phys. Rev. 140, B516 (1965), https://doi.org/10.1103/PhysRev.140.B516, p. B521, Sec. III, Eqs. (3.2)–(3.3)

import Definitions.Def_Weinberg1965_Defs

namespace Weinberg1965

theorem photon_massless_divergence {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ι → ℝ) (p : ι → Vec3) (e η : ι → ℝ) (i₁ : ι)
    (hm₁ : m i₁ = 0) (hm : ∀ n, n ≠ i₁ → 0 < m n) (hp₁ : p i₁ ≠ 0)
    (hη : ∀ n, η n = 1 ∨ η n = -1)
    (hcharge : ∑ n, η n * e n = 0) (he₁ : e i₁ ≠ 0) :
    Filter.Tendsto (fun μ : ℝ => photonIndex (Function.update m i₁ μ) p e η)
      (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop := by
  sorry

end Weinberg1965
