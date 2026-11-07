-- Prove2me | Theorems.Thm_VecBalPoly_lemma_4_4
-- name    : VecBalPoly.lemma_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T23:09:43.807614+00:00
-- url     : https://prove2.me/theorems/9efccf5c-f002-4341-9d9e-81e416811182
-- title:
--   Lemma 4.4 — the restricted-trace lemma
-- statement:
--   Let $S\succeq0$ and let $D\succeq0$ be diagonal on $\mathbb R^s$. Suppose $S_{jj}\le\rho D_{jj}$ for every $j$, where $\rho\ge0$. Then every subspace $\mathcal H\subseteq\mathbb R^s$ with $\dim\mathcal H>\rho s$ contains a nonzero vector $h$ with
--   $$h^{\mathsf T}(S-D)h\le0.$$
--
--   Proposition 4.5 applies it to compare the positive curvature of the exponential weights with the concavity of the barriers.
--
--   Differences from the source:
--   - encoding: D ⪰ 0 diagonal → D = diag(δ) with δ_j ≥ 0; reason: a diagonal matrix is positive semidefinite exactly when its diagonal is nonnegative
--   - encoding: indices j ∈ [s] → Fin s (0-based); reason: Lean convention; same instances
-- source:
--   S. Guo, E. X. Fang, J. Lu, Vector Balancing in Polynomial Time, arXiv:2609.23540 (held file sha256 b777ade4…), Lemma 4.4, p.10 (PDF p.11); proof in Appendix B, p.14

import Mathlib

namespace VecBalPoly

open Matrix

/-- **Lemma 4.4 (restricted trace lemma).**
Guo, Fang, Lu, *Vector Balancing in Polynomial Time*, arXiv:2609.23540 (held file sha256
b777ade4…), Lemma 4.4, p.10 (PDF p.11): "Let S ⪰ 0 and let D ⪰ 0 be diagonal on ℝ^s. Suppose
Sjj ≤ ρDjj for every j, where ρ ≥ 0. Every subspace H ⊆ ℝ^s with dim H > ρs contains a nonzero
vector h with hᵀ(S − D)h ≤ 0."

**Formalization Note** `D = diag(δ)` with `δ ≥ 0` is a positive semidefinite diagonal
matrix. -/
theorem lemma_4_4 :
    ∀ (s : ℕ) (S : Matrix (Fin s) (Fin s) ℝ) (δ : Fin s → ℝ) (ρ : ℝ), S.PosSemidef →
      (∀ j, 0 ≤ δ j) → 0 ≤ ρ → (∀ j, S j j ≤ ρ * δ j) →
      ∀ H : Submodule ℝ (Fin s → ℝ), ρ * s < (Module.finrank ℝ H : ℝ) →
        ∃ h ∈ H, h ≠ 0 ∧ h ⬝ᵥ ((S - Matrix.diagonal δ) *ᵥ h) ≤ 0 := by sorry

end VecBalPoly
