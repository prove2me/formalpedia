-- Prove2me | Theorems.Thm_StengelZeroSum_Supplement_lemma_1
-- name    : StengelZeroSum.Supplement.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T03:28:09.506603+00:00
-- url     : https://prove2.me/theorems/bbaf7d44-5154-4638-8a33-37c5461d9754
-- title:
--   Lemma 1 — $Ax=b$ has no solution iff some $y$ has $y^\top A=0^\top$ and $y^\top b\neq0$
-- statement:
--   Let $A$ be a real $m\times n$ matrix ($m,n\ge1$) and $b\in\mathbb R^m$. Then
--
--   $$
--   \nexists\,x\in\mathbb R^n:\ Ax=b
--   \quad\Longleftrightarrow\quad
--   \exists\,y\in\mathbb R^m:\ y^\top A=\mathbf 0^\top,\ y^\top b\neq0 . \tag{22}
--   $$
--
--   This theorem of the alternative for linear equations without sign constraints says that the null space and row space of a matrix are orthogonal complements. The paper uses it in the proof of Stiemke's Theorem 3 and in Section 10 for a short proof of the Lemma of Farkas.
--
--   Differences from the source: none.
-- source:
--   von Stengel, Zero-Sum Games and Linear Programming Duality, arXiv:2205.11196v6, Lemma 1, eq. (22), p.10

import Mathlib

open Matrix

namespace StengelZeroSum.Supplement

/-- **Lemma 1**, von Stengel, *Zero-Sum Games and Linear Programming Duality*, arXiv:2205.11196v6, Lemma 1, eq. (22), p.10: for `A ∈ ℝ^{m×n}` and `b ∈ ℝ^m`,
`∄ x ∈ ℝ^n : Ax = b  ⇔  ∃ y ∈ ℝ^m : y⊤A = 0⊤, y⊤b ≠ 0`.

**Formalization Note** `y⊤A` is `y ᵥ* A` and `y⊤b` is `y ⬝ᵥ b`. `0 < m`, `0 < n` are the
standing assumption (p.4). -/
theorem lemma_1 {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) :
    (¬ ∃ x : Fin n → ℝ, A *ᵥ x = b) ↔ ∃ y : Fin m → ℝ, y ᵥ* A = 0 ∧ y ⬝ᵥ b ≠ 0 := by sorry

end StengelZeroSum.Supplement
