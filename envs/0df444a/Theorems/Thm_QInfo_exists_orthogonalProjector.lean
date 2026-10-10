-- Prove2me | Theorems.Thm_QInfo_exists_orthogonalProjector
-- name    : QInfo.exists_orthogonalProjector
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-09T14:44:33.111979+00:00
-- url     : https://prove2.me/theorems/e012a196-646e-493a-833b-d8396ec0e68f
-- title:
--   Every subspace of $\mathbb C^\iota$ has an orthogonal projector matrix
-- statement:
--   Let $\iota$ be a finite index type and $C \subseteq \mathbb C^\iota$ a complex linear subspace (e.g. a quantum code subspace). Then there is a matrix $P$ which is the orthogonal projector onto $C$:
--   $$P^\dagger = P,\qquad P^2 = P,\qquad P v \in C \ \text{for all } v,\qquad P v = v \ \text{for all } v\in C .$$
--
--   This is the projector $P$ onto the code subspace used throughout Almheiri–Dong–Harlow (e.g. Eqs. (3.19)–(3.21) and Appendix B).
--
--   **Formalization Note.** The matrix acts on vectors via `Matrix.mulVec` (`P *ᵥ v`); Hermiticity is `Matrix.IsHermitian`.
-- source:
--   Almheiri, Dong, Harlow, Bulk Locality and Quantum Error Correction in AdS/CFT, JHEP 04 (2015) 163, https://arxiv.org/abs/1411.7041, Appendix B (projector $P$ onto the code subspace, Sec. 3.2 and App. B)

import Mathlib
open Matrix

namespace QInfo
theorem exists_orthogonalProjector {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Submodule ℂ (ι → ℂ)) :
    ∃ P : Matrix ι ι ℂ, P.IsHermitian ∧ P * P = P ∧ (∀ v, P *ᵥ v ∈ C) ∧
      ∀ v ∈ C, P *ᵥ v = v := by sorry
end QInfo
