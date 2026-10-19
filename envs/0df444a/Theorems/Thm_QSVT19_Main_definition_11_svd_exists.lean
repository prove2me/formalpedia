-- Prove2me | Theorems.Thm_QSVT19_Main_definition_11_svd_exists
-- name    : QSVT19.Main.definition_11_svd_exists
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:28:25.671363+00:00
-- url     : https://prove2.me/theorems/755eca4a-197b-41d6-ba8b-58cf75802f87
-- title:
--   Definition 11: a projected unitary has a singular value decomposition over $\mathrm{img}\,\Pi$ and $\mathrm{img}\,\widetilde\Pi$
-- statement:
--   Let $U$ be a unitary and $\Pi,\widetilde\Pi$ orthogonal projectors on a finite-dimensional Hilbert space, and $A=\widetilde\Pi U\Pi$. With $d=\operatorname{rank}\Pi$, $\tilde d=\operatorname{rank}\widetilde\Pi$ and $d_{\min}=\min(d,\tilde d)$, there are orthonormal bases $(\psi_i)_{i\in[d]}$ of $\mathrm{img}\,\Pi$ and $(\tilde\psi_i)_{i\in[\tilde d]}$ of $\mathrm{img}\,\widetilde\Pi$, and reals $\varsigma_1\ge\dots\ge\varsigma_{d_{\min}}\ge0$, such that
--   $$A=\sum_{i=1}^{d_{\min}}\varsigma_i\,|\tilde\psi_i\rangle\langle\psi_i|.$$
--
--   This is the existence claim behind Definition 11; it guarantees that statements quantified over all such decompositions (Theorem 17, Corollary 18) are not vacuous.
-- source:
--   Gilyén, Su, Low, Wiebe, arXiv:1806.01838v1, p. 15, Definition 11, (17)

import Definitions.Def_QSVT19_Main_Setting

set_option autoImplicit false

open scoped ComplexOrder
open Polynomial Matrix

namespace QSVT19.Main

/-- Gilyén, Su, Low, Wiebe, arXiv:1806.01838v1, Definition 11, p. 15 (existence claim): "Let H_U be a finite-dimensional Hilbert space and
let U, Π, Π̃ ∈ End(H_U) be linear operators on H_U such that U is a unitary, and Π, Π̃ are
orthogonal projectors, and let A = Π̃UΠ. Let d := rank(Π), d̃ := rank(Π̃), d_min := min(d, d̃). By
singular value decomposition we know that there exist orthonormal bases (|ψ_i⟩ : i ∈ [d]),
(|ψ̃_i⟩ : i ∈ [d̃]) of the subspaces img(Π) and img(Π̃) respectively, such that
A = ∑_{i=1}^{d_min} ς_i|ψ̃_i⟩⟨ψ_i|, (17) and for all i ∈ [d_min]: ς_i ∈ R^+_0. Moreover,
ς_i ≥ ς_j for all i ≤ j ∈ [d_min]."

**Formalization Note.** `H_U` is `ι → ℂ` for a finite type `ι`, with inner product
`star v ⬝ᵥ w`; `Π, Π̃` are `Proj, Projt`; "unitary" is `U ∈ Matrix.unitaryGroup ι ℂ` and
"orthogonal projector" is `IsStarProjection` (self-adjoint idempotent). A term of `ProjUnitarySVD U Proj Projt` is exactly such a decomposition (see its
docstring); the statement also records `d = rank Π` and `d̃ = rank Π̃`. This claim shows that the
quantification over decompositions in Theorem 17 and Corollary 18 is not vacuous. -/
theorem definition_11_svd_exists {ι : Type*} [Fintype ι] [DecidableEq ι] (U Proj Projt : Matrix ι ι ℂ) (hU : U ∈ Matrix.unitaryGroup ι ℂ) (hProj : IsStarProjection Proj) (hProjt : IsStarProjection Projt) :
    ∃ S : ProjUnitarySVD U Proj Projt, S.d = Proj.rank ∧ S.dt = Projt.rank := by sorry

end QSVT19.Main
