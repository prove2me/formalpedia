-- Prove2me | Theorems.Thm_ROLDescent_lemma_2_3
-- name    : ROLDescent.lemma_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T21:45:08.934001+00:00
-- url     : https://prove2.me/theorems/69918e62-324c-4fad-8fe4-325640eee74a
-- title:
--   Lemma 2.3 — Gram norm and projection sum: $C\succeq0$, $\|C\|=\|\mathsf S\|^2=\|\sum_iE_i\|$
-- statement:
--   Let $\mathcal U_1, \dots, \mathcal U_m$ be subspaces of a finite-dimensional complex Hilbert space $\mathcal H$ with isometric inclusions $J_i$, summation map $\mathsf S((u_i)_i) = \sum_i J_i u_i$ on the orthogonal direct sum, and Gram operator $C = \mathsf S^* \mathsf S$. Then $E_i = J_i J_i^*$ is the orthogonal projection onto $\mathcal U_i$, and
--
--   $$C \succeq 0, \qquad \|C\| = \|\mathsf S\|^2 = \Big\| \sum_i E_i \Big\|, \qquad \Big\| \sum_i J_i u_i \Big\|^2 \le \|C\| \sum_i \|u_i\|^2 .$$
--
--   This converts the norm of a projection sum into a bound for sums of vectors taken from the subspaces; it is used, with weights, inside the one-step Gram estimate.
--
--   **Formalization Note** The direct sum is `PiLp 2 (fun i => U i)` over a finite index type; $C \succeq 0$ is Mathlib's `IsPositive` (self-adjoint with nonnegative quadratic form).
--
--   Differences from the source:
--   - encoding: orthogonal direct sum ⊕_i U_i of U_1, …, U_m → PiLp 2 (fun i => U i) over an arbitrary finite index type ι; reason: the ℓ²-product is the orthogonal direct sum; ι plays the role of {1, …, m}, and the empty family (m = 0, S = 0) satisfies every clause trivially
-- source:
--   Hayakawa, Recursive Operator Localization and Spectral Gap Descent via the Geometry of Local Spectral Expansion, arXiv:2610.23695 (held version, sha256 702bd512…20bdd545), Lemma 2.3, eq. (8), p.10 (PDF 10)

import Mathlib
import Definitions.Def_ROLDescent_sumMap

namespace ROLDescent

/-- **Lemma 2.3 (Gram norm and projection sum).** Hayakawa, *Recursive Operator Localization and Spectral Gap Descent via the Geometry of Local
Spectral Expansion*, arXiv:2610.23695 (held version, sha256 702bd512…20bdd545), Lemma 2.3, eq. (8), p.10 (PDF 10):
"For the data of Definition 2.2, let E_i = J_i J_i* be the orthogonal projection onto U_i. Then
C ⪰ 0, ‖C‖ = ‖S‖² = ‖Σ_i E_i‖, ‖Σ_i J_i u_i‖² ≤ ‖C‖ Σ_i ‖u_i‖²."

**Formalization Note** `J_i` is `(U i).subtypeL`, `S` is `sumMap U` on `PiLp 2 (fun i => U i)`,
`C = S† S`. The first conjunct is the clause "E_i = J_i J_i* is the orthogonal projection onto U_i". -/
theorem lemma_2_3 {ι : Type*} [Fintype ι]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (U : ι → Submodule ℂ H) :
    (∀ i, (U i).subtypeL ∘L ContinuousLinearMap.adjoint (U i).subtypeL = (U i).starProjection) ∧
    (ContinuousLinearMap.adjoint (sumMap U) ∘L sumMap U).IsPositive ∧
    ‖ContinuousLinearMap.adjoint (sumMap U) ∘L sumMap U‖ = ‖sumMap U‖ ^ 2 ∧
    ‖sumMap U‖ ^ 2 = ‖∑ i, (U i).starProjection‖ ∧
    (∀ u : PiLp 2 (fun i => ↥(U i)),
      ‖∑ i, ((u i : ↥(U i)) : H)‖ ^ 2 ≤
        ‖ContinuousLinearMap.adjoint (sumMap U) ∘L sumMap U‖ * ∑ i, ‖u i‖ ^ 2) := by sorry

end ROLDescent
