-- Prove2me | Theorems.Thm_UndecidableSpectralGap_usg_switch_sector_spectrum_bounds
-- name    : UndecidableSpectralGap.usg_switch_sector_spectrum_bounds
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-22T18:16:39.335118+00:00
-- url     : https://prove2.me/theorems/c36d4871-f0ce-4546-9f3a-28b95df46caa
-- title:
--   Three-state switch sector eigenvalues and spectral lower bound
-- statement:
--   Let $0<b\le 1/2$, $|a|\le b$, and let $L\ge2$. For the finite-volume three-state switch Hamiltonian $H_L(a,b)$, both the vacuum energy $0$ and the all-occupied ferromagnetic energy $aL^2$ occur in the real spectrum, and every spectral value $\mu$ satisfies
--
--   $$\min(0,aL^2)\le\mu.$$
--
--   This theorem packages the vacuum/occupied sector eigenvectors with the positivity estimate that controls the bottom of the complete finite-volume spectrum.
-- source:
--   Original auxiliary specialization of the vacuum/occupied-sector construction in Cubitt–Pérez-García–Wolf, arXiv:1502.04573v5, Section 6.2, equations (130a)–(130d); the occupied-row interaction is twice the spin-1/2 Hamiltonian in Napiórkowski–Seiringer, doi:10.1007/s11005-021-01375-4, equation (2.1).

import Definitions.Def_usg_three_state_switch

set_option autoImplicit false
open UndecidableSpectralGap

theorem UndecidableSpectralGap.usg_switch_sector_spectrum_bounds
    (b a : ℝ) (hb : 0 < b) (hbhalf : b ≤ 1 / 2) (ha : |a| ≤ b) :
    ∀ L : ℕ, 2 ≤ L →
      0 ∈ specReal (switchHam L a b) ∧
      a * (L : ℝ) ^ 2 ∈ specReal (switchHam L a b) ∧
      ∀ μ ∈ specReal (switchHam L a b),
        min 0 (a * (L : ℝ) ^ 2) ≤ μ := by sorry
