-- Prove2me | Theorems.Thm_QuadMatIneq_Stabilization_theorem_4_10
-- name    : QuadMatIneq.Stabilization.theorem_4_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:13:28.853161+00:00
-- url     : https://prove2.me/theorems/f37747d6-46ee-4c4d-8fd2-7515643dc981
-- title:
--   Theorem 4.10 (Strict matrix S-lemma) — for N ∈ 𝚷_{q,r} with N₂₂ < 0, 𝒵_r(N) ⊆ 𝒵_r^+(M) iff M − αN > 0 for some α ⩾ 0
-- statement:
--   Let $M,N\in\mathbb{S}^{q+r}$.
--
--   1. If there exists $\alpha\geqslant 0$ with $M-\alpha N>0$, then $\mathcal Z_r(N)\subseteq\mathcal Z_r^+(M)$.
--   2. If moreover $N\in\boldsymbol\Pi_{q,r}$ and $N_{22}<0$, then
--   $$\mathcal Z_r(N)\subseteq\mathcal Z_r^+(M)\iff\exists\,\alpha\geqslant 0:\ M-\alpha N>0 .$$
--
--   The strict matrix S-lemma; part (b) of Theorem 5.1 rests on it.
--
--
--   **Formalization Note** Matrices $M,N\in\mathbb{S}^{q+r}$ are real matrices indexed by `ι ⊕ κ` with $q=|\iota|$, $r=|\kappa|$ (the first block is $q\times q$, the second $r\times r$); "$\in\mathbb{S}$" is `IsHermitian`, $A\geqslant 0$ is `PosSemidef` and $A>0$ is `PosDef` (both include symmetry, as in §1.1 of the paper); $\mathcal Z_r(\cdot)$, $\mathcal Z_r^+(\cdot)$, $\mathcal Z_r^0(\cdot)$ and $\boldsymbol\Pi_{q,r}$ are `ZSet`, `ZPlus`, `ZZero`, `InPi` of the definitions item `QuadMatIneq.Stabilization.QMI`.
-- source:
--   van Waarde–Camlibel–Eising–Trentelman, arXiv:2203.12959v3, Theorem 4.10, p. 13

import Mathlib
import Definitions.Def_QuadMatIneq_Stabilization_QMI

open Matrix

namespace QuadMatIneq.Stabilization

/-- Theorem 4.10 (Strict matrix S-lemma), p. 13. -/
theorem theorem_4_10 {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (M N : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (hM : M.IsHermitian) (hN : N.IsHermitian) :
    ((∃ α : ℝ, 0 ≤ α ∧ (M - α • N).PosDef) → ZSet N ⊆ ZPlus M) ∧
    (InPi N → (-N.toBlocks₂₂).PosDef →
      (ZSet N ⊆ ZPlus M ↔ ∃ α : ℝ, 0 ≤ α ∧ (M - α • N).PosDef)) := by sorry

end QuadMatIneq.Stabilization
