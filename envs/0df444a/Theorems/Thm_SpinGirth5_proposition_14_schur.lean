-- Prove2me | Theorems.Thm_SpinGirth5_proposition_14_schur
-- name    : SpinGirth5.proposition_14_schur
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:11:44.525916+00:00
-- url     : https://prove2.me/theorems/010b81a4-ce60-4e04-b4c9-47517b3d49c9
-- title:
--   Proposition 14 — Schur complement criterion: $A\succeq0\iff A/A_{00}\succeq0$
-- statement:
--   Let $H=H_0\oplus H_1$ be an orthogonal decomposition of a finite-dimensional real inner-product space, and let $A:H\to H$ be self-adjoint with $A_{00}\succ 0$, i.e. $\langle x,Ax\rangle>0$ for every nonzero $x\in H_0$. Then
--   $$A\succeq 0\iff A/A_{00}\succeq 0,$$
--   where $A/A_{00}=A_{11}-A_{10}A_{00}^{-1}A_{01}$ is the Schur complement and $\succeq 0$ means self-adjoint with nonnegative quadratic form.
--
--   This reduces positivity of an operator on $H_0\oplus H_1$ to positivity of an operator on $H_1$; the proof of Theorem 25 applies it twice on the Hoeffding blocks of a star.
--
--   Differences from the source:
--   - encoding: orthogonal decomposition H = H₀ ⊕ H₁ → H₁ := H₀ᗮ for a subspace H₀; reason: in finite dimension the orthogonal complement is the only orthogonal complementary subspace
--   - encoding: A₀₀⁻¹ → Ring.inverse in the endomorphism ring of H₀; reason: A₀₀ ≻ 0 makes A₀₀ invertible, where Ring.inverse is the inverse
--   - encoding: A ⪰ 0 (Definition 11) → LinearMap.IsPositive (self-adjoint with ⟨Ax, x⟩ ≥ 0); reason: the same definition
-- source:
--   Chen, Liu, A Spectral Local-to-Global Principle for Spin Systems on Graphs with Girth At Least Five, arXiv:2608.25491, Proposition 14, Eq. (5), p.11 (Definition 13, Eq. (4), p.11)

import Mathlib
import Definitions.Def_SpinGirth5_schurComplement

namespace SpinGirth5

/-- **Proposition 14** (Schur complement criterion). Let `H = H₀ ⊕ H₁` be an orthogonal
decomposition of a finite-dimensional real inner-product space (`H₁ = H₀ᗮ`) and let `A : H → H`
be self-adjoint with `A₀₀ ≻ 0`. Then `A ⪰ 0 ⟺ A/A₀₀ ⪰ 0`.

Chen, Liu, *A Spectral Local-to-Global Principle for Spin Systems on Graphs with Girth At Least
Five*, arXiv:2608.25491, Proposition 14, Eq. (5), p.11.

**Formalization Note** `A₀₀ ≻ 0` is `⟨x, A x⟩ > 0` for every nonzero `x ∈ H₀`, which is
`⟨x, A₀₀ x⟩ > 0` since `x ∈ H₀`. `⪰ 0` is Mathlib's `LinearMap.IsPositive` (self-adjoint with
nonnegative quadratic form), the paper's Definition 11. -/
theorem proposition_14_schur {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] (A : H →ₗ[ℝ] H) (hA : A.IsSymmetric) (H₀ : Submodule ℝ H)
    (hA₀₀ : ∀ x : H₀, x ≠ 0 → 0 < inner ℝ (x : H) (A x)) :
    A.IsPositive ↔ (schurComplement A H₀).IsPositive := by sorry

end SpinGirth5
