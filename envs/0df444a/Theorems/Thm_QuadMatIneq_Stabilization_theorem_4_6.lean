-- Prove2me | Theorems.Thm_QuadMatIneq_Stabilization_theorem_4_6
-- name    : QuadMatIneq.Stabilization.theorem_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:14:34.326517+00:00
-- url     : https://prove2.me/theorems/b61ac890-43f3-4d96-8e54-97c9916a71ac
-- title:
--   Theorem 4.6 — for N ∈ 𝚷_{q,r}, the inclusions 𝒵_r(N) ⊆ 𝒵_r(M) and 𝒵_r(N) ⊆ 𝒵_r^+(M) are equivalent to vector implications
-- statement:
--   Let $M,N\in\mathbb{S}^{q+r}$ with $N\in\boldsymbol\Pi_{q,r}$.
--
--   1. If $N$ has at least one positive eigenvalue, then
--   $$\mathcal Z_r(N)\subseteq\mathcal Z_r(M)\iff z^\top Mz\geqslant 0\ \text{ for all } z\in\mathbb{R}^{q+r} \text{ with } z^\top Nz\geqslant 0 .$$
--   2. If $N_{22}<0$, then
--   $$\mathcal Z_r(N)\subseteq\mathcal Z_r^+(M)\iff z^\top Mz>0\ \text{ for all nonzero } z\in\mathbb{R}^{q+r} \text{ with } z^\top Nz\geqslant 0 .$$
--
--   This theorem reduces matrix-valued inclusions of QMI solution sets to vector-valued implications between quadratic forms, to which the classical S-lemmas apply.
--
--
--   **Formalization Note** Matrices $M,N\in\mathbb{S}^{q+r}$ are real matrices indexed by `ι ⊕ κ` with $q=|\iota|$, $r=|\kappa|$ (the first block is $q\times q$, the second $r\times r$); "$\in\mathbb{S}$" is `IsHermitian`, $A\geqslant 0$ is `PosSemidef` and $A>0$ is `PosDef` (both include symmetry, as in §1.1 of the paper); $\mathcal Z_r(\cdot)$, $\mathcal Z_r^+(\cdot)$, $\mathcal Z_r^0(\cdot)$ and $\boldsymbol\Pi_{q,r}$ are `ZSet`, `ZPlus`, `ZZero`, `InPi` of the definitions item `QuadMatIneq.Stabilization.QMI`.
-- source:
--   van Waarde–Camlibel–Eising–Trentelman, arXiv:2203.12959v3, Theorem 4.6, p. 11

import Mathlib
import Definitions.Def_QuadMatIneq_Stabilization_QMI

open Matrix

namespace QuadMatIneq.Stabilization

/-- Theorem 4.6, p. 11. -/
theorem theorem_4_6 {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (M N : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (hM : M.IsHermitian) (hN : N.IsHermitian) (hNPi : InPi N) :
    ((∃ i, 0 < hN.eigenvalues i) →
      (ZSet N ⊆ ZSet M ↔
        ∀ z : ι ⊕ κ → ℝ, 0 ≤ z ⬝ᵥ (N *ᵥ z) → 0 ≤ z ⬝ᵥ (M *ᵥ z))) ∧
    ((-N.toBlocks₂₂).PosDef →
      (ZSet N ⊆ ZPlus M ↔
        ∀ z : ι ⊕ κ → ℝ, z ≠ 0 → 0 ≤ z ⬝ᵥ (N *ᵥ z) → 0 < z ⬝ᵥ (M *ᵥ z))) := by sorry

end QuadMatIneq.Stabilization
