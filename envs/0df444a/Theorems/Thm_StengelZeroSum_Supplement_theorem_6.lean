-- Prove2me | Theorems.Thm_StengelZeroSum_Supplement_theorem_6
-- name    : StengelZeroSum.Supplement.theorem_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T03:29:56.026916+00:00
-- url     : https://prove2.me/theorems/2661315b-9971-5551-92a7-e511fb4324f9
-- title:
--   Theorem 6 — Gordan's Theorem (20) for all matrices implies Tucker's Theorem (39) for all matrices
-- statement:
--   Theorem 6 states: Gordan's Theorem (20) proves Tucker's Theorem (39). Formally: suppose that for all $m,n\ge1$ and every real $m\times n$ matrix $A$,
--
--   $$
--   \nexists\,x\in\mathbb R^n:\ Ax=\mathbf 0,\ x\ge\mathbf 0,\ x\neq\mathbf 0
--   \quad\Longleftrightarrow\quad
--   \exists\,y\in\mathbb R^m:\ y^\top A>\mathbf 0^\top . \tag{20}
--   $$
--
--   Then for all $m,n\ge1$ and every real $m\times n$ matrix $A$ there exist $y\in\mathbb R^m$, $x\in\mathbb R^n$ with
--
--   $$
--   y^\top A\ge\mathbf 0^\top,\qquad x\ge\mathbf 0,\qquad Ax=\mathbf 0,\qquad x^\top+y^\top A>\mathbf 0^\top . \tag{39}
--   $$
--
--   The hypothesis ranges over all matrices, not only the conclusion's $A$, because the paper's proof applies Gordan's Theorem to a different matrix obtained by eliminating the variables on the maximal support. Since Tucker's Theorem is true, the implication is also provable from its conclusion alone; the paper's contribution is the proof that uses only Gordan's Theorem, which, with Proposition 4, gives a proof of LP duality from the minimax theorem.
--
--   **Formalization Note** (20) and (39) are the definitions `Gordan20` and `Tucker39`.
--
--   Differences from the source:
--   - reading: "Gordan's Theorem (20) proves Tucker's Theorem (39)" → (∀ m n ≥ 1, ∀ A, Gordan20 A) → (∀ m n ≥ 1, ∀ A, Tucker39 A); reason: the informal "proves" between two theorems is read as implication between their universal statements; the proof (pp.16–17) applies (20) to a matrix D of size (m − k) × |J| with both dimensions positive, so the hypothesis must cover all matrices of positive dimensions.
-- source:
--   von Stengel, Zero-Sum Games and Linear Programming Duality, arXiv:2205.11196v6, Theorem 6, p.15 (proof pp.16–17; (20) p.9, (39) p.15)

import Mathlib
import Definitions.Def_StengelZeroSum_Supplement_Gordan20
import Definitions.Def_StengelZeroSum_Supplement_Tucker39

open Matrix

namespace StengelZeroSum.Supplement

/-- **Theorem 6**, von Stengel, *Zero-Sum Games and Linear Programming Duality*, arXiv:2205.11196v6, Theorem 6, p.15: "Gordan's Theorem (20) proves Tucker's Theorem (39)."

Stated as an implication between the two theorems, each quantified over all real matrices of
positive dimensions: if Gordan's equivalence (20) holds for every `A ∈ ℝ^{m×n}` (all
`m, n ≥ 1`), then Tucker's Theorem (39) holds for every `A ∈ ℝ^{m×n}` (all `m, n ≥ 1`).

**Formalization Note** The hypothesis must range over all matrices, not only the conclusion's
`A`: the proof (pp.16–17) applies Gordan's Theorem to a different matrix `D` of size
`(m − k) × |J|` (both positive in the proof). Since both theorems are true, this implication is
also provable from Tucker's Theorem alone; the paper's contribution is the proof from Gordan's
Theorem. `Gordan20`, `Tucker39` are the definitions of (20), (39). -/
theorem theorem_6 :
    (∀ (m n : ℕ), 0 < m → 0 < n → ∀ A : Matrix (Fin m) (Fin n) ℝ, Gordan20 A) →
      ∀ (m n : ℕ), 0 < m → 0 < n → ∀ A : Matrix (Fin m) (Fin n) ℝ, Tucker39 A := by sorry

end StengelZeroSum.Supplement
