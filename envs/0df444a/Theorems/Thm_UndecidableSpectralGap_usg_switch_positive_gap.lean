-- Prove2me | Theorems.Thm_UndecidableSpectralGap_usg_switch_positive_gap
-- name    : UndecidableSpectralGap.usg_switch_positive_gap
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-22T18:16:24.188812+00:00
-- url     : https://prove2.me/theorems/3a6b3f1b-59c3-4eb5-ac66-f9b6d825078a
-- title:
--   Three-state switch vacuum uniqueness and unit spectral gap
-- statement:
--   Let $0<b\le1/2$, $|a|\le b$, and $L\ge2$. If the all-occupied sector shift satisfies $aL^2\ge1$, then the vacuum is the unique zero-energy state of $H_L(a,b)$ and every nonzero real eigenvalue is at least one:
--
--   $$\operatorname{mult}_{H_L(a,b)}(0)=1,\qquad \mu\ne0\Longrightarrow\mu\ge1.$$
--
--   This separates the conditional finite-volume gap estimate from the explicit sector eigenvalue and magnon constructions.
-- source:
--   Original auxiliary specialization of the vacuum/occupied-sector construction in Cubitt–Pérez-García–Wolf, arXiv:1502.04573v5, Section 6.2, equations (130a)–(130d), using the explicit guarded three-state Hamiltonian of Definitions.Def_usg_three_state_switch.

import Definitions.Def_usg_three_state_switch

set_option autoImplicit false
open UndecidableSpectralGap

theorem UndecidableSpectralGap.usg_switch_positive_gap
    (b a : ℝ) (hb : 0 < b) (hbhalf : b ≤ 1 / 2) (ha : |a| ≤ b) :
    ∀ L : ℕ, 2 ≤ L →
      1 ≤ a * (L : ℝ) ^ 2 →
        eigMultiplicity (switchHam L a b) 0 = 1 ∧
        ∀ μ ∈ specReal (switchHam L a b), μ ≠ 0 → 1 ≤ μ := by sorry
