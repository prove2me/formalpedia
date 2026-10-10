-- Prove2me | Theorems.Thm_QuadMatIneq_Stabilization_theorem_4_7
-- name    : QuadMatIneq.Stabilization.theorem_4_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:13:48.088532+00:00
-- url     : https://prove2.me/theorems/2cb63ce7-58c3-4274-aed1-185d2ab5ff3c
-- title:
--   Theorem 4.7 (Matrix S-lemma) — for N ∈ 𝚷_{q,r} with a positive eigenvalue, 𝒵_r(N) ⊆ 𝒵_r(M) iff M − αN ⩾ 0 for some α ⩾ 0
-- statement:
--   Let $M,N\in\mathbb{S}^{q+r}$.
--
--   1. If there exists $\alpha\geqslant 0$ with $M-\alpha N\geqslant 0$, then $\mathcal Z_r(N)\subseteq\mathcal Z_r(M)$.
--   2. If moreover $N\in\boldsymbol\Pi_{q,r}$ and $N$ has at least one positive eigenvalue, then
--   $$\mathcal Z_r(N)\subseteq\mathcal Z_r(M)\iff\exists\,\alpha\geqslant 0:\ M-\alpha N\geqslant 0 .$$
--
--   The matrix S-lemma characterizes when every solution of one QMI solves another by a linear matrix inequality in a single scalar multiplier.
--
--
--   **Formalization Note** Matrices $M,N\in\mathbb{S}^{q+r}$ are real matrices indexed by `ι ⊕ κ` with $q=|\iota|$, $r=|\kappa|$ (the first block is $q\times q$, the second $r\times r$); "$\in\mathbb{S}$" is `IsHermitian`, $A\geqslant 0$ is `PosSemidef` and $A>0$ is `PosDef` (both include symmetry, as in §1.1 of the paper); $\mathcal Z_r(\cdot)$, $\mathcal Z_r^+(\cdot)$, $\mathcal Z_r^0(\cdot)$ and $\boldsymbol\Pi_{q,r}$ are `ZSet`, `ZPlus`, `ZZero`, `InPi` of the definitions item `QuadMatIneq.Stabilization.QMI`.
-- source:
--   van Waarde–Camlibel–Eising–Trentelman, arXiv:2203.12959v3, Theorem 4.7, p. 12

import Mathlib
import Definitions.Def_QuadMatIneq_Stabilization_QMI

open Matrix

namespace QuadMatIneq.Stabilization

/-- Theorem 4.7 (Matrix S-lemma), p. 12. -/
theorem theorem_4_7 {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (M N : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (hM : M.IsHermitian) (hN : N.IsHermitian) :
    ((∃ α : ℝ, 0 ≤ α ∧ (M - α • N).PosSemidef) → ZSet N ⊆ ZSet M) ∧
    (InPi N → (∃ i, 0 < hN.eigenvalues i) →
      (ZSet N ⊆ ZSet M ↔ ∃ α : ℝ, 0 ≤ α ∧ (M - α • N).PosSemidef)) := by sorry

end QuadMatIneq.Stabilization
