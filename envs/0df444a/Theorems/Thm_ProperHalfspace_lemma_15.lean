-- Prove2me | Theorems.Thm_ProperHalfspace_lemma_15
-- name    : ProperHalfspace.lemma_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:01:55.130809+00:00
-- url     : https://prove2.me/theorems/3b37bdaa-2ab1-40ce-9ab5-a0ff641e2844
-- title:
--   Lemma 15 — the top eigenspace of a positive semidefinite matrix of trace at most one
-- statement:
--   Let $M\succeq0$ with $\mathrm{Tr}(M)\le1$, let $\lambda>0$ and $E=\mathrm{Eigen}_\lambda(M)$. Then:
--
--   1. $\dim(E)\le\lambda^{-1}$;
--   2. $\Pi_E\preceq M/\lambda$;
--   3. every unit vector $v\in E^\perp$ satisfies $v^\top Mv\le\lambda$;
--   4. if $M_{ii}\le t_{\mathrm{diag}}$ for every $i$, every unit vector $u\in E$ satisfies $\|u\|_\infty\le\sqrt{t_{\mathrm{diag}}/\lambda}$.
--
--   This records the spectral properties the learner uses.
--
--   Differences from the source:
--   - encoding: M indexed by [n] → M indexed by a generic finite type; reason: every finite type is a relabelling of some [n]; Lemma 19 applies the lemma to a principal submatrix
--   - encoding: Π_E ⪯ M/λ → x^⊤ Π_E x ≤ λ⁻¹ x^⊤ M x for all x; reason: the definition of the Loewner order, written as forms
-- source:
--   De, Mossel, Nadimpalli, Neeman, Efficient Proper Agnostic Learning of Halfspaces, arXiv:2611.02344 (Nov. 1, 2026), Lemma 15, p.20

import Mathlib
import Definitions.Def_ProperHalfspace_TopEigenspace

namespace ProperHalfspace

/-- Lemma 15, p.20. De, Mossel, Nadimpalli, Neeman, arXiv:2611.02344 (Nov. 1, 2026). For `M ⪰ 0` with `Tr M ≤ 1`, `λ > 0` and
`E = Eigen_λ(M)`: `dim E ≤ λ⁻¹`; `Π_E ⪯ M/λ`; every unit `v ∈ E⊥` has `v^⊤ M v ≤ λ`; and if `M_ii ≤ t_diag` for every `i`, then every
unit `u ∈ E` has `‖u‖_∞ ≤ √(t_diag/λ)`.

**Formalization Note.** `Π_E ⪯ M/λ` is written as the quadratic-form inequality `x^⊤ Π_E x ≤ λ⁻¹ x^⊤ M x` for all `x`. The index type
is generic because Lemma 19 applies this to a principal submatrix. -/
theorem lemma_15 {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) (hM : M.PosSemidef)
    (htr : M.trace ≤ 1) (lamE : ℝ) (hlam : 0 < lamE) :
    (Module.finrank ℝ (topEigenspace M lamE) : ℝ) ≤ lamE⁻¹ ∧
    (∀ x : EuclideanSpace ℝ ι,
      inner ℝ x ((topEigenspace M lamE).starProjection x) ≤ lamE⁻¹ * quadForm M x) ∧
    (∀ v ∈ (topEigenspace M lamE)ᗮ, ‖v‖ = 1 → quadForm M v ≤ lamE) ∧
    (∀ tdiag : ℝ, (∀ i, M i i ≤ tdiag) → ∀ u ∈ topEigenspace M lamE, ‖u‖ = 1 →
      ∀ i, |u i| ≤ Real.sqrt (tdiag / lamE)) := by sorry

end ProperHalfspace
