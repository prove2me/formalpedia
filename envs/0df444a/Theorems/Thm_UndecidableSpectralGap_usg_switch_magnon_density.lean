-- Prove2me | Theorems.Thm_UndecidableSpectralGap_usg_switch_magnon_density
-- name    : UndecidableSpectralGap.usg_switch_magnon_density
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-21T20:27:30.55041+00:00
-- url     : https://prove2.me/theorems/be8d3c34-19af-4dc6-8649-aa016f4b310c
-- title:
--   Independent-row magnon sums uniformly approximate a unit interval
-- statement:
--   Fix b>0. For every tolerance δ>0, all sufficiently large L have the property
--
--   $$\forall x\in[0,1]\quad\exists s\in S_L(b): |x-s|\le\delta.$$
--
--   Here S_L(b) consists of sums of L numbers 2b(1−cos(πk/L)), with independently chosen integers 0≤k<L. This is a real-analysis statement about finite trigonometric grids; it does not assume a Hamiltonian spectrum or a halting predicate.
-- source:
--   Original auxiliary specialization of the vacuum/occupied-sector construction in Cubitt–Pérez-García–Wolf, arXiv:1502.04573v5, Section 6.2, equations (130a)–(130d). The occupied row interaction is twice the spin-1/2 Hamiltonian of Napiórkowski–Seiringer, Free energy asymptotics of the quantum Heisenberg spin chain, https://doi.org/10.1007/s11005-021-01375-4, equation (2.1). This is a concrete auxiliary model, not a restatement of either paper’s undecidability theorem.

import Definitions.Def_usg_three_state_switch

set_option autoImplicit false
open UndecidableSpectralGap

theorem UndecidableSpectralGap.usg_switch_magnon_density
    (b : ℝ) (hb : 0 < b) :
    ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ L > N,
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        ∃ s ∈ switchMagnonSpectrum L b, |x - s| ≤ δ := by sorry
