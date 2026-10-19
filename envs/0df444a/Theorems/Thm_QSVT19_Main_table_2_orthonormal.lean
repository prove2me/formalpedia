-- Prove2me | Theorems.Thm_QSVT19_Main_table_2_orthonormal
-- name    : QSVT19.Main.table_2_orthonormal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:28:24.658984+00:00
-- url     : https://prove2.me/theorems/ccc0f67a-672a-4ddf-866f-b99007bc1310
-- title:
--   Table 2: the spanning vectors of the invariant subspaces form an orthonormal system
-- statement:
--   Let $U$ be unitary, $\Pi,\widetilde\Pi$ orthogonal projectors, and fix a singular value decomposition $A=\widetilde\Pi U\Pi=\sum_{i}\varsigma_i|\tilde\psi_i\rangle\langle\psi_i|$ as in Definition 11. Define, for $0<\varsigma_i<1$,
--   $$|\psi_i^\perp\rangle=\frac{(I-\Pi)U^\dagger|\tilde\psi_i\rangle}{\sqrt{1-\varsigma_i^2}},\qquad|\tilde\psi_i^\perp\rangle=\frac{(I-\widetilde\Pi)U|\psi_i\rangle}{\sqrt{1-\varsigma_i^2}}.$$
--   Then the vectors
--   1. $|\psi_i\rangle$ ($i\in[d]$), $|\psi_i^\perp\rangle$ ($0<\varsigma_i<1$) and $U^\dagger|\tilde\psi_j\rangle$ ($j\in[\tilde d]$ with $\varsigma_j=0$) form an orthonormal system, and
--   2. symmetrically, $|\tilde\psi_j\rangle$ ($j\in[\tilde d]$), $|\tilde\psi_i^\perp\rangle$ ($0<\varsigma_i<1$) and $U|\psi_j\rangle$ ($j\in[d]$ with $\varsigma_j=0$) form an orthonormal system,
--
--   where $\varsigma_i:=0$ beyond $d_{\min}$. Hence the subspaces $\mathcal H_i$, $\mathcal H_i^R$, $\mathcal H_i^L$ of Definition 12 are pairwise orthogonal.
--
--   **Formalization Note** The paper's index sets $[r]\setminus[k]$ and $[\tilde d]\setminus[r]$ ($k$ the last index with $\varsigma_k=1$, $r$ the rank of $A$) are written as $0<\varsigma_i<1$ and $\varsigma_j=0$, which they equal because the singular values are non-increasing in $[0,1]$.
-- source:
--   Gilyén, Su, Low, Wiebe, arXiv:1806.01838v1, p. 15–16, §3.2 after Definition 12, Table 2, (18)–(23)

import Definitions.Def_QSVT19_Main_Setting

set_option autoImplicit false

open scoped ComplexOrder
open Polynomial Matrix

namespace QSVT19.Main

/-- Gilyén, Su, Low, Wiebe, arXiv:1806.01838v1, §3.2, p. 15, and Table 2, p. 16: "Now we show that the subspaces H_i : i ∈ [k],
H_i : i ∈ [r] \ [k], H^R_i : i ∈ [d] \ [r] and H^L_i : i ∈ [d̃] \ [r] are indeed pairwise orthogonal,
by proving that their spanning bases described in Definition 12 form an orthonormal system of
vectors. (By symmetry it also implies that the spanning bases of the H̃ subspaces form also an
orthonormal system of vectors.)"

**Formalization Note.** `H_U` is `ι → ℂ` for a finite type `ι`, with inner product
`star v ⬝ᵥ w`; `Π, Π̃` are `Proj, Projt`; "unitary" is `U ∈ Matrix.unitaryGroup ι ℂ` and
"orthogonal projector" is `IsStarProjection` (self-adjoint idempotent). The spanning vectors of Definition 12 are `S.orthoFamily` (all `|ψ_i⟩`, the
`|ψ_i^⊥⟩` for `0 < ς_i < 1`, the `U^†|ψ̃_j⟩` for `ς_j = 0`, `ς` extended by zero) and
`S.orthoFamilyTilde` (all `|ψ̃_j⟩`, the `|ψ̃_i^⊥⟩`, the `U|ψ_j⟩` for `ς_j = 0`); "orthonormal
system" is `⟨a|b⟩ = δ_{ab}` over the disjoint union of the three index sets. The predicates
`0 < ς_i < 1` and `ς_j = 0` replace the paper's `[r] \ [k]` and `[d̃] \ [r]`, which they equal
because the `ς_i` are non-increasing in `[0, 1]`. Both the stated system and the symmetric one are
included. -/
theorem table_2_orthonormal {ι : Type*} [Fintype ι] [DecidableEq ι] (U Proj Projt : Matrix ι ι ℂ) (hU : U ∈ Matrix.unitaryGroup ι ℂ) (hProj : IsStarProjection Proj) (hProjt : IsStarProjection Projt) (S : ProjUnitarySVD U Proj Projt) :
    (∀ a b, star (S.orthoFamily a) ⬝ᵥ S.orthoFamily b = if a = b then 1 else 0) ∧ (∀ a b, star (S.orthoFamilyTilde a) ⬝ᵥ S.orthoFamilyTilde b = if a = b then 1 else 0) := by sorry

end QSVT19.Main
