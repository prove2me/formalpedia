-- Prove2me | Theorems.Thm_QuditSymCircuits_FermionLaw_picomp_perm_comm
-- name    : QuditSymCircuits.FermionLaw.picomp_perm_comm
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:31:56.779295+00:00
-- url     : https://prove2.me/theorems/2e3f455b-ebd0-48bd-ae55-fdc0f5a61168
-- title:
--   p. 9, below Eq. (42) — Π_comp commutes with every permutation P(σ)
-- statement:
--   For every permutation $\sigma\in S_n$ of the $n$ qudits, the orthogonal projector $\Pi_{\mathrm{comp}}$ onto $\mathcal H_{\mathrm{comp}}$ commutes with $\mathbf P(\sigma)$:
--   $$\mathbf P(\sigma)\,\Pi_{\mathrm{comp}} = \Pi_{\mathrm{comp}}\,\mathbf P(\sigma).$$
--
--   This expresses that $\mathcal H_{\mathrm{comp}}$ is invariant under permutations of the qudits; in particular every SU(d)-invariant unitary, a linear combination of permutations, preserves $\mathcal H_{\mathrm{comp}}$.
-- source:
--   Marvian, Liu and Hulse, Qudit circuits with SU(d) symmetry, arXiv:2105.12877v2, p. 9, the two sentences below Eq. (42)

import Mathlib
import Definitions.Def_QuditSymCircuits_FermionLaw_Model

open scoped Matrix
open QuditSymCircuits.FermionLaw QAlgorithms.Entanglement

namespace QuditSymCircuits.FermionLaw

theorem picomp_perm_comm (n d : ℕ) [NeZero d] (σ : Equiv.Perm (Fin n)) :
    (permOp σ : Op n d) * Picomp n d = Picomp n d * permOp σ := by sorry

end QuditSymCircuits.FermionLaw
