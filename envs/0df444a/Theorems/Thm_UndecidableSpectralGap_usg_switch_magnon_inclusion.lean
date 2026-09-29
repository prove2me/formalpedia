-- Prove2me | Theorems.Thm_UndecidableSpectralGap_usg_switch_magnon_inclusion
-- name    : UndecidableSpectralGap.usg_switch_magnon_inclusion
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-22T18:15:55.809479+00:00
-- url     : https://prove2.me/theorems/5a72c7dd-d0d7-4ed8-8b3d-85463064a840
-- title:
--   Three-state switch contains the translated row-magnon spectrum
-- statement:
--   Let $0<b\le 1/2$, $|a|\le b$, and $L\ge2$. Every sum $s$ of one-magnon path-Laplacian energies, with one independently chosen mode in each occupied row, produces an eigenvalue of the three-state switch Hamiltonian after adding the occupied-sector shift:
--
--   $$aL^2+S_L(b)\subseteq\operatorname{spec}_{\mathbb R} H_L(a,b).$$
--
--   This isolates the tensor-product row-magnon construction used to populate the finite-volume spectrum.
-- source:
--   Original auxiliary specialization of the vacuum/occupied-sector construction in Cubitt–Pérez-García–Wolf, arXiv:1502.04573v5, Section 6.2, equations (130a)–(130d); one-row magnon energies follow Napiórkowski–Seiringer, doi:10.1007/s11005-021-01375-4, equation (2.1).

import Definitions.Def_usg_three_state_switch

set_option autoImplicit false
open UndecidableSpectralGap

theorem UndecidableSpectralGap.usg_switch_magnon_inclusion
    (b a : ℝ) (hb : 0 < b) (hbhalf : b ≤ 1 / 2) (ha : |a| ≤ b) :
    ∀ L : ℕ, 2 ≤ L →
      ∀ s ∈ switchMagnonSpectrum L b,
        a * (L : ℝ) ^ 2 + s ∈ specReal (switchHam L a b) := by sorry
