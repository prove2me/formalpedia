-- Prove2me | Theorems.Thm_UndecidableSpectralGap_usg_switch_finite_spectrum
-- name    : UndecidableSpectralGap.usg_switch_finite_spectrum
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-21T20:27:23.69139+00:00
-- url     : https://prove2.me/theorems/d219c152-a21d-4ba6-82b6-91f74e6b4f33
-- title:
--   Three-state switch: norm and finite-volume spectral bounds
-- statement:
--   For positive b≤1/2 and |a|≤b, the three-state switch has local interaction strength at most one. For every L≥2, put E=aL². Its spectrum contains zero and E, is bounded below by min(0,E), and contains the translated row-magnon set:
--
--   $$E+S_L(b)\subseteq\operatorname{spec}_{\mathbb R}H_L(a,b).$$
--
--   If E≥1, zero has multiplicity one and all other eigenvalues are at least one. These finite-dimensional bounds are independent of any machine or halting predicate. The lower size cutoff excludes the empty lattice and the one-site graph.
-- source:
--   Original auxiliary specialization of the vacuum/occupied-sector construction in Cubitt–Pérez-García–Wolf, arXiv:1502.04573v5, Section 6.2, equations (130a)–(130d). The occupied row interaction is twice the spin-1/2 Hamiltonian of Napiórkowski–Seiringer, Free energy asymptotics of the quantum Heisenberg spin chain, https://doi.org/10.1007/s11005-021-01375-4, equation (2.1). This is a concrete auxiliary model, not a restatement of either paper’s undecidability theorem.

import Definitions.Def_usg_three_state_switch

set_option autoImplicit false
open UndecidableSpectralGap

theorem UndecidableSpectralGap.usg_switch_finite_spectrum
    (b a : ℝ) (hb : 0 < b) (hbhalf : b ≤ 1 / 2) (ha : |a| ≤ b) :
    localInteractionStrength ((a : ℂ) • switchProjector)
      (switchGuard + (b : ℂ) • switchExchange) switchGuard ≤ 1 ∧
    ∀ L : ℕ, 2 ≤ L →
      (0 ∈ specReal (switchHam L a b) ∧
       a * (L : ℝ) ^ 2 ∈ specReal (switchHam L a b) ∧
       ∀ μ ∈ specReal (switchHam L a b), min 0 (a * (L : ℝ) ^ 2) ≤ μ) ∧
      (∀ s ∈ switchMagnonSpectrum L b,
        a * (L : ℝ) ^ 2 + s ∈ specReal (switchHam L a b)) ∧
      (1 ≤ a * (L : ℝ) ^ 2 → eigMultiplicity (switchHam L a b) 0 = 1 ∧
        ∀ μ ∈ specReal (switchHam L a b), μ ≠ 0 → 1 ≤ μ) := by sorry
