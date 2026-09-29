-- Prove2me | Theorems.Thm_UndecidableSpectralGap_usg_switch_entrywise_laplacian
-- name    : UndecidableSpectralGap.usg_switch_entrywise_laplacian
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-22T23:11:10.737669+00:00
-- url     : https://prove2.me/theorems/6a81e52d-643b-4c8d-8723-c546d66b8156
-- title:
--   Computational-basis Laplacian formula for the three-state switch
-- statement:
--   For every lattice size and arbitrary real parameters a,b, the computational-basis matrix entries satisfy
--
--   $$H_{cc}=V_a(c)+\sum_{j\ne c}W_b(c,j),\qquad H_{cc′}=-W_b(c,c′)\quad(c\ne c′).$$
--
--   The potential and rates are the explicit occupation, boundary and occupied-spin transposition counts. This is an entrywise identity, with no eigenvalue, positivity or gap assumptions. It includes the empty and one-site lattices.
-- source:
--   Original auxiliary specialization of the vacuum/occupied-sector construction in Cubitt–Pérez-García–Wolf, arXiv:1502.04573v5, Section 6.2, equations (130a)–(130d); the occupied-row interaction is twice the spin-1/2 Hamiltonian in Napiórkowski–Seiringer, doi:10.1007/s11005-021-01375-4, equation (2.1). Explicit computational-basis expansion: each occupied unequal-spin horizontal edge contributes the 2-by-2 Laplacian [[1,-1],[-1,1]], and each vacuum/occupied edge contributes one to the diagonal.

import Definitions.Def_usg_switch_entry_data
set_option autoImplicit false
open UndecidableSpectralGap

theorem UndecidableSpectralGap.usg_switch_entrywise_laplacian
    (L : ℕ) (a b : ℝ) (c c' : Config L 3) :
    switchHam L a b c c' =
      if c = c' then
        ((switchPotential L a c +
          ∑ j ∈ Finset.univ.erase c, switchTransitionRate L b c j : ℝ) : ℂ)
      else -((switchTransitionRate L b c c' : ℝ) : ℂ) := by sorry
