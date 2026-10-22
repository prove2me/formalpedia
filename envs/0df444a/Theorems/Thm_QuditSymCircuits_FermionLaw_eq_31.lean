-- Prove2me | Theorems.Thm_QuditSymCircuits_FermionLaw_eq_31
-- name    : QuditSymCircuits.FermionLaw.eq_31
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:31:43.661806+00:00
-- url     : https://prove2.me/theorems/d3ab3b03-f950-40c4-b7cc-6ed3ee6a980f
-- title:
--   Eq. (31), p. 8 — e^{iθP^f_ab} acts on creation operators as a single-particle rotation
-- statement:
--   For sites $a,b,j$ and $\theta\in[0,2\pi)$, the fermionic swap $\mathbf P^f_{ab}$ satisfies
--   $$e^{i\theta\mathbf P^f_{ab}}\,c_j^\dagger\,e^{-i\theta\mathbf P^f_{ab}} = e^{-i\theta}\big(\cos\theta\,c_j^\dagger + i\sin\theta\,c^\dagger_{\sigma_{ab}(j)}\big).$$
--
--   The right-hand side is linear in the creation operators, so the Hamiltonian $\mathbf P^f_{ab}$ is free (non-interacting).
--
--   **Formalization Note.** $e^{\pm i\theta\mathbf P^f_{ab}}$ is written in the closed form $\cos\theta\,\mathbb I^f \pm i\sin\theta\,\mathbf P^f_{ab}$, valid because $\mathbf P^f_{ab}$ is an involution.
-- source:
--   Marvian, Liu and Hulse, Qudit circuits with SU(d) symmetry, arXiv:2105.12877v2, p. 8, Eq. (31); proof App. C2, Eq. (C15), p. 28

import Mathlib
import Definitions.Def_QuditSymCircuits_FermionLaw_Model

open scoped Matrix
open QuditSymCircuits.FermionLaw QAlgorithms.Entanglement

namespace QuditSymCircuits.FermionLaw

theorem eq_31 (n : ℕ) (a b j : Fin n) (θ : ℝ) (hθ : θ ∈ Set.Ico 0 (2 * Real.pi)) :
    expInv θ (Pf a b) * cdag j * expInv (-θ) (Pf a b) =
      Complex.exp (-(θ : ℂ) * Complex.I) •
        ((Real.cos θ : ℂ) • cdag j + (Complex.I * (Real.sin θ : ℂ)) • cdag (Equiv.swap a b j)) := by sorry

end QuditSymCircuits.FermionLaw
