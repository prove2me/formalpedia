-- Prove2me | Theorems.Thm_WildeQIT_Purification_convex_decompositions_related_by_isometry
-- name    : WildeQIT.Purification.convex_decompositions_related_by_isometry
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:20:03.343151+00:00
-- url     : https://prove2.me/theorems/6ff9f224-efac-496a-951d-95b9e108bb9c
-- title:
--   Two convex decompositions of a density operator are related by an isometry (Corollary 5.1.1)
-- statement:
--   Let $\rho$ be an operator on a finite-dimensional Hilbert space $\mathcal H_A$ with two convex decompositions into pure states,
--
--   $$
--   \rho = \sum_{x=1}^{d} p_X(x)\,|\psi_x\rangle\langle\psi_x| = \sum_{y=1}^{d'} p_Y(y)\,|\varphi_y\rangle\langle\varphi_y|,
--   $$
--
--   where $p_X$ and $p_Y$ are probability distributions on $\{1,\dots,d\}$ and $\{1,\dots,d'\}$, every $|\psi_x\rangle$ and $|\varphi_y\rangle$ is a unit vector, and $d'\le d$. Then there exists an isometry $U$, a $d\times d'$ matrix with $U^\dagger U = I_{d'}$, such that for every $x$
--
--   $$
--   \sqrt{p_X(x)}\,|\psi_x\rangle = \sum_{y} U_{x,y}\,\sqrt{p_Y(y)}\,|\varphi_y\rangle .
--   $$
--
--   This answers the question of when two ensembles give the same density operator: their weighted vectors are related by an isometry.
--
--   **Formalization Note** $|\psi\rangle\langle\psi|$ is the matrix with entries $\psi(i)\overline{\psi(j)}$. The matrix $U$ has rows indexed by $x$ and columns by $y$; the isometry condition is the published predicate `HarlowTASI.IsIsometry` ($U^\dagger U = 1$).
--
--   Differences from the source:
--   - encoding: indices $x\in\{1,\dots,d\}$, $y\in\{1,\dots,d'\}$ → `Fin d`, `Fin d'` (0-based); reason: Lean convention; same families.
--   - encoding: "$\rho$ a density operator" as a separate hypothesis → no separate hypothesis; reason: either convex decomposition into unit vectors with probability weights forces $\rho$ to be positive semidefinite with unit trace, so no instance changes.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Corollary 5.1.1, eqs. (5.10)–(5.11), p. 186

import Mathlib
import Definitions.Def_HarlowTASI_QuantumBasics

namespace WildeQIT.Purification

/-- **Corollary 5.1.1 (convex decompositions of a density operator are related by an
isometry).** Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8,
Corollary 5.1.1, p. 186: "Let two convex decompositions of a density operator ρ be as follows:
ρ = Σ_{x=1}^{d} p_X(x)|ψ_x⟩⟨ψ_x| = Σ_{y=1}^{d′} p_Y(y)|φ_y⟩⟨φ_y|, (5.10) where d′ ≤ d. Then there
exists an isometry U such that √p_X(x)|ψ_x⟩ = Σ_y U_{x,y} √p_Y(y)|φ_y⟩." (5.11)

`p_X : Fin d → ℝ` and `p_Y : Fin d' → ℝ` are probability distributions, `ψ x`, `φ y : a → ℂ`
are unit vectors (pure states), and `ρ` equals both mixtures. The isometry is
`U : Matrix (Fin d) (Fin d') ℂ`, rows indexed by `x` and columns by `y`, with
`HarlowTASI.IsIsometry U`, i.e. `Uᴴ U = I_{d'}` (the book's Definition 4.6.3, p. 162).

**Formalization Note.** Indices run over `Fin d`, `Fin d'` (0-based) instead of
`{1, …, d}`, `{1, …, d'}`. That `ρ` is a density operator follows from the two decompositions.
`|ψ⟩⟨ψ|` is `vecMulVec ψ (star ψ)`. -/
theorem convex_decompositions_related_by_isometry {a : Type} [Fintype a] {d d' : ℕ}
    (hd : d' ≤ d) (ρ : Matrix a a ℂ)
    (pX : Fin d → ℝ) (pY : Fin d' → ℝ) (ψ : Fin d → a → ℂ) (φ : Fin d' → a → ℂ)
    (hpX_nonneg : ∀ x, 0 ≤ pX x) (hpX_sum : ∑ x, pX x = 1)
    (hpY_nonneg : ∀ y, 0 ≤ pY y) (hpY_sum : ∑ y, pY y = 1)
    (hψ : ∀ x, ∑ i, Complex.normSq (ψ x i) = 1) (hφ : ∀ y, ∑ i, Complex.normSq (φ y i) = 1)
    (hρX : ρ = ∑ x, (pX x : ℂ) • Matrix.vecMulVec (ψ x) (star (ψ x)))
    (hρY : ρ = ∑ y, (pY y : ℂ) • Matrix.vecMulVec (φ y) (star (φ y))) :
    ∃ U : Matrix (Fin d) (Fin d') ℂ, HarlowTASI.IsIsometry U ∧
      ∀ x, (Real.sqrt (pX x) : ℂ) • ψ x = ∑ y, (U x y * (Real.sqrt (pY y) : ℂ)) • φ y := by sorry

end WildeQIT.Purification
