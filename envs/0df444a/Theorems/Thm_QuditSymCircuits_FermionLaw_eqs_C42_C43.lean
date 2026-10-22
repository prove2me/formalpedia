-- Prove2me | Theorems.Thm_QuditSymCircuits_FermionLaw_eqs_C42_C43
-- name    : QuditSymCircuits.FermionLaw.eqs_C42_C43
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:31:41.322906+00:00
-- url     : https://prove2.me/theorems/74849f86-11ce-4c81-8da2-345fdda5c2fb
-- title:
--   App. C7, Eqs. (C42)–(C43), p. 32 — the qudit form (51) and the fermionic form (50) of Ω agree
-- statement:
--   With $Q_{ij} = (\mathbb I_i-|0\rangle\langle0|_i)|0\rangle\langle 0|_j$:
--
--   1. for all sites $i\ne j$, $\;\Pi_{\mathrm{comp}}\mathbf P_{ij}Q_{ij}\Pi_{\mathrm{comp}} = \Pi_{\mathrm{comp}}U^{f\dagger}c_j^\dagger c_iU^f\Pi_{\mathrm{comp}}$ (C42);
--   2. for every site $k$, $\;\Pi_{\mathrm{comp}}(\mathbb I_k-|0\rangle\langle 0|_k)\Pi_{\mathrm{comp}} = \Pi_{\mathrm{comp}}U^{f\dagger}c_k^\dagger c_kU^f\Pi_{\mathrm{comp}}$ (C43);
--   3. consequently, for every operator $\rho$ on $(\mathbb C^d)^{\otimes n}$,
--   $$\mathrm{Tr}\big(c_j^\dagger c_i\,U^f\Pi_{\mathrm{comp}}\rho\,\Pi_{\mathrm{comp}}U^{f\dagger}\big) = \Omega_{ij}[\rho]\quad\text{for all } i,j,$$
--   i.e. the definitions (50) and (51) of $\Omega$ agree.
--
--   This is the dictionary that turns the qudit map $\Omega$ into the single-particle reduced state of the fermionic system.
-- source:
--   Marvian, Liu and Hulse, Qudit circuits with SU(d) symmetry, arXiv:2105.12877v2, p. 32, App. C7, Eqs. (50), (51), (C42), (C43)

import Mathlib
import Definitions.Def_QuditSymCircuits_FermionLaw_Model

open scoped Matrix
open QuditSymCircuits.FermionLaw QAlgorithms.Entanglement

namespace QuditSymCircuits.FermionLaw

theorem eqs_C42_C43 (n d : ℕ) [NeZero d] :
    (∀ i j : Fin n, i ≠ j →
      Picomp n d * (swapOp i j * Qop i j) * Picomp n d =
        Picomp n d * (Uf n d)ᴴ * cdag j * cop i * Uf n d * Picomp n d) ∧
    (∀ k : Fin n,
      Picomp n d * localOp k (1 - ket0bra0) * Picomp n d =
        Picomp n d * (Uf n d)ᴴ * cdag k * cop k * Uf n d * Picomp n d) ∧
    (∀ ρ : Op n d, omegaF n d ρ = omega n d ρ) := by sorry

end QuditSymCircuits.FermionLaw
