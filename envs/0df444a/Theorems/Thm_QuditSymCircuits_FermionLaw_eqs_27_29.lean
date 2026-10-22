-- Prove2me | Theorems.Thm_QuditSymCircuits_FermionLaw_eqs_27_29
-- name    : QuditSymCircuits.FermionLaw.eqs_27_29
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:31:39.590177+00:00
-- url     : https://prove2.me/theorems/49b7b19c-5018-46d1-91cb-37ba38b8b7f7
-- title:
--   Eqs. (27)–(29), p. 8 — the fermionic swap P^f_ab represents the transposition and fixes the vacuum
-- statement:
--   On the fermionic Fock space of $n$ sites let $\mathbf P^f_{ab} = \mathbb I^f - (c_a^\dagger-c_b^\dagger)(c_a-c_b)$. Then
--
--   1. $\mathbf P^f_{ab}\,c_j^\dagger\,\mathbf P^{f\,\dagger}_{ab} = c^\dagger_{\sigma_{ab}(j)}$ for every site $j$, where $\sigma_{ab}$ is the transposition of $a$ and $b$ (Eq. (27));
--   2. $\mathbf P^f_{ab}|\mathrm{vac}\rangle = |\mathrm{vac}\rangle$ (Eq. (29));
--   3. $\mathbf P^f_{ab}$ is Hermitian and unitary: $\mathbf P^{f\,\dagger}_{ab} = \mathbf P^f_{ab}$ and $(\mathbf P^f_{ab})^2 = \mathbb I^f$.
--
--   The fermionic swap is the operator through which the action of qudit swaps on $\mathcal H_{\mathrm{comp}}$ becomes a free-fermion evolution.
--
--   **Formalization Note.** The uniqueness claim of App. C1 is not part of the statement. $a = b$ is allowed ($\mathbf P^f_{aa} = \mathbb I^f$).
-- source:
--   Marvian, Liu and Hulse, Qudit circuits with SU(d) symmetry, arXiv:2105.12877v2, p. 8, Eqs. (27)–(29) and the sentence after (29); proof App. C1, p. 27

import Mathlib
import Definitions.Def_QuditSymCircuits_FermionLaw_Model

open scoped Matrix
open QuditSymCircuits.FermionLaw QAlgorithms.Entanglement

namespace QuditSymCircuits.FermionLaw

theorem eqs_27_29 (n : ℕ) (a b : Fin n) :
    (∀ j : Fin n, Pf a b * cdag j * (Pf a b)ᴴ = cdag (Equiv.swap a b j)) ∧
      Pf a b *ᵥ (vac : Finset (Fin n) → ℂ) = vac ∧
      (Pf a b)ᴴ = Pf a b ∧ Pf a b * Pf a b = 1 := by sorry

end QuditSymCircuits.FermionLaw
