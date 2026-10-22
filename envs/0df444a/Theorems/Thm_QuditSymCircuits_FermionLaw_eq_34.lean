-- Prove2me | Theorems.Thm_QuditSymCircuits_FermionLaw_eq_34
-- name    : QuditSymCircuits.FermionLaw.eq_34
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:31:39.552366+00:00
-- url     : https://prove2.me/theorems/d5ca464c-7ef8-493a-b8c3-585ba8b9e8d1
-- title:
--   Eq. (34), p. 8 — single-particle form: e^{iθ(P^f_ab − I^f)} c†_j e^{−iθ(P^f_ab − I^f)} = Σ_l ⟨l|e^{iθ(E_ab − I)}|j⟩ c†_l
-- statement:
--   Let $E_{ab} = \mathbb I - (|a\rangle-|b\rangle)(\langle a|-\langle b|)$ on $\mathbb C^n$. For all sites $a,b,j$ and $\theta\in[0,2\pi)$,
--   $$e^{i\theta(\mathbf P^f_{ab}-\mathbb I^f)}\,c_j^\dagger\,e^{-i\theta(\mathbf P^f_{ab}-\mathbb I^f)} = \sum_{l=1}^n\langle l|\,e^{i\theta(E_{ab}-\mathbb I)}\,|j\rangle\;c_l^\dagger.$$
--
--   The fermionic swap dynamics on creation operators is thus the single-particle unitary $e^{i\theta(E_{ab}-\mathbb I)}$ on $\mathbb C^n$.
--
--   **Formalization Note.** For an involution $X$, $e^{i\theta(X-\mathbb I)}$ is written as $e^{-i\theta}(\cos\theta\,\mathbb I + i\sin\theta\,X)$; this applies to both $\mathbf P^f_{ab}$ and $E_{ab}$.
-- source:
--   Marvian, Liu and Hulse, Qudit circuits with SU(d) symmetry, arXiv:2105.12877v2, p. 8, Eq. (34)

import Mathlib
import Definitions.Def_QuditSymCircuits_FermionLaw_Model

open scoped Matrix
open QuditSymCircuits.FermionLaw QAlgorithms.Entanglement

namespace QuditSymCircuits.FermionLaw

theorem eq_34 (n : ℕ) (a b j : Fin n) (θ : ℝ) (hθ : θ ∈ Set.Ico 0 (2 * Real.pi)) :
    expShift θ (Pf a b) * cdag j * expShift (-θ) (Pf a b) =
      ∑ l : Fin n, (expShift θ (Eab a b)) l j • cdag l := by sorry

end QuditSymCircuits.FermionLaw
