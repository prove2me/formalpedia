-- Prove2me | Theorems.Thm_QuditSymCircuits_FermionLaw_eq_41
-- name    : QuditSymCircuits.FermionLaw.eq_41
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:31:36.633988+00:00
-- url     : https://prove2.me/theorems/38540f6a-5a8c-4050-b239-494823ee43ae
-- title:
--   Eq. (41) and App. C5, pp. 9, 31 — U^f maps P(σ)[(∧|m⟩)⊗|0⟩^{⊗(n−L)}] to ∏ c†_{σ(i)}|vac⟩ and is an isometry on H_comp
-- statement:
--   Let $U^f$ be the qudit–fermion map. Then
--
--   1. for every $L\le\min\{n,d-1\}$ and every $\sigma\in S_n$,
--   $$U^f\,\mathbf P(\sigma)\Big[\Big(\bigwedge_{m=1}^{L}|m\rangle\Big)\otimes|0\rangle^{\otimes(n-L)}\Big] = \prod_{i=1}^{L}c^\dagger_{\sigma(i)}|\mathrm{vac}\rangle,$$
--   the product read with $i=1$ leftmost (Eq. (41));
--   2. $U^f$ preserves inner products on $\mathcal H_{\mathrm{comp}}$: $(U^f\Pi_{\mathrm{comp}})^\dagger(U^f\Pi_{\mathrm{comp}}) = \Pi_{\mathrm{comp}}$.
--
--   This identifies $\mathcal H_{\mathrm{comp}}$ with a subspace of the fermionic Fock space, the $L$-particle sectors for $L\le\min\{n,d-1\}$.
--
--   **Formalization Note.** The paper claims there exists a linear isometry with property (41). Here $U^f$ is the explicit linear map defined in the Model (sending the basis state with $|m\rangle$ on site $p(m)$ to $\frac1{\sqrt{L!}}c^\dagger_{p(1)}\cdots c^\dagger_{p(L)}|\mathrm{vac}\rangle$), which is that witness; it is defined on all of $(\mathbb C^d)^{\otimes n}$, so the isometry is stated on $\mathcal H_{\mathrm{comp}}$. Eq. (41) holds with the representation convention for $\mathbf P(\sigma)$ (see the Model's Formalization Note).
-- source:
--   Marvian, Liu and Hulse, Qudit circuits with SU(d) symmetry, arXiv:2105.12877v2, p. 9, Eq. (41) and the sentence after it; App. C5, p. 31

import Mathlib
import Definitions.Def_QuditSymCircuits_FermionLaw_Model

open scoped Matrix
open QuditSymCircuits.FermionLaw QAlgorithms.Entanglement

namespace QuditSymCircuits.FermionLaw

theorem eq_41 (n d : ℕ) [NeZero d] :
    (∀ (L : ℕ) (hLn : L ≤ n), L + 1 ≤ d → ∀ σ : Equiv.Perm (Fin n),
      Uf n d *ᵥ ((permOp σ : Op n d) *ᵥ phiState L) =
        cdagProdVac (fun i : Fin L => σ (Fin.castLE hLn i))) ∧
    (Uf n d * Picomp n d)ᴴ * (Uf n d * Picomp n d) = Picomp n d := by sorry

end QuditSymCircuits.FermionLaw
