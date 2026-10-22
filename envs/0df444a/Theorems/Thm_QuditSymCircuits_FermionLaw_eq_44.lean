-- Prove2me | Theorems.Thm_QuditSymCircuits_FermionLaw_eq_44
-- name    : QuditSymCircuits.FermionLaw.eq_44
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:31:39.730759+00:00
-- url     : https://prove2.me/theorems/a9b667e9-d48a-419a-81c6-94881c52baa5
-- title:
--   Eq. (44), p. 10 — U^f e^{iθP_ab} Π_comp = e^{iθP^f_ab} U^f Π_comp
-- statement:
--   For all sites $a,b$ and $\theta\in[0,2\pi)$,
--   $$U^f\,e^{i\theta\mathbf P_{ab}}\,\Pi_{\mathrm{comp}} = e^{i\theta\mathbf P^f_{ab}}\,U^f\,\Pi_{\mathrm{comp}}.$$
--
--   Inside $\mathcal H_{\mathrm{comp}}$, the qudit swap Hamiltonian $\mathbf P_{ab}$ is thereby equivalent to the free fermionic Hamiltonian $\mathbf P^f_{ab}$.
--
--   **Formalization Note.** Both exponentials are in the closed form $\cos\theta\,\mathbb I + i\sin\theta\,X$. The general intertwining (43) for arbitrary $\sigma$ is not stated, as it would need the whole fermionic representation $\mathbf P^f(\sigma)$.
-- source:
--   Marvian, Liu and Hulse, Qudit circuits with SU(d) symmetry, arXiv:2105.12877v2, p. 10, Eq. (44)

import Mathlib
import Definitions.Def_QuditSymCircuits_FermionLaw_Model

open scoped Matrix
open QuditSymCircuits.FermionLaw QAlgorithms.Entanglement

namespace QuditSymCircuits.FermionLaw

theorem eq_44 (n d : ℕ) [NeZero d] (a b : Fin n) (θ : ℝ)
    (hθ : θ ∈ Set.Ico 0 (2 * Real.pi)) :
    Uf n d * expInv θ (swapOp a b : Op n d) * Picomp n d =
      expInv θ (Pf a b) * Uf n d * Picomp n d := by sorry

end QuditSymCircuits.FermionLaw
