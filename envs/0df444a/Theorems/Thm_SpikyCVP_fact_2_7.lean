-- Prove2me | Theorems.Thm_SpikyCVP_fact_2_7
-- name    : SpikyCVP.fact_2_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T04:43:20.303195+00:00
-- url     : https://prove2.me/theorems/0b5df15e-a655-4b6d-9cb5-dcaf895ddf7b
-- title:
--   Fact 2.7 — cosets of $2\mathcal L$ in a lattice
-- statement:
--   Let $\mathcal L=\mathcal L(B)$ be a lattice of rank $n$, with $B\in\mathbb R^{m\times n}$ having linearly independent columns.
--
--   1. $\mathcal L$ is the disjoint union of the $2^n$ cosets $2\mathcal L+Bc$, $c\in\{0,1\}^n$: each coset lies in $\mathcal L$, and every $x\in\mathcal L$ lies in exactly one of them.
--   2. If $x$ and $y$ lie in the same coset, then $\frac{x+y}{2}\in\mathcal L$.
--   3. If moreover $\mathcal L\subseteq\mathbb Z^m$ and $x\ne y$ lie in the same coset, then $\|x-y\|_2\ge2$.
--
--   The algorithm runs once for each of the $2^n$ cosets, and these three facts are what the analysis uses about the coset containing a closest vector.
--
--   Differences from the source:
--   - encoding: L is the disjoint union of the 2ⁿ cosets 2L + Bc, c ∈ {0,1}ⁿ → every coset 2L + Bc (c : Fin n → Fin 2) lies in L, and every x ∈ L lies in exactly one of them; reason: equivalent; the 2ⁿ cosets are distinct because Bc lies in 2L + Bc
--   - encoding: L ⊆ Z^m → every vector of L has integer coordinates (a hypothesis of item 3); reason: the same condition
-- source:
--   Aggarwal, Morolia, How to Round Spiky Balls into Submission; And Faster Algorithms For The Closest Vector Problem, STOC 2027 submission (manuscript sha256 535c3bcc…), Fact 2.7, p.14 (PDF p.16)

import Mathlib
import Definitions.Def_PNormReg_Norms
import Definitions.Def_SpikyCVP_latt

open PNormReg

namespace SpikyCVP

/-- **Fact 2.7 (Cosets of a Lattice).**
Aggarwal, Morolia, *How to Round Spiky Balls into Submission; And Faster Algorithms For The Closest Vector
Problem*, STOC 2027 submission (manuscript sha256 535c3bcc…), Fact 2.7, p.14 (PDF p.16).

Let `L = L(B)` be a lattice of rank `n`, `B ∈ ℝ^{m×n}` with linearly independent columns.
1. `L` is the disjoint union of the `2ⁿ` cosets `2L + Bc`, `c ∈ {0,1}ⁿ`: each coset lies in `L`, and each
   `x ∈ L` lies in exactly one of them.
2. If `x` and `y` lie in the same coset, then `(x + y)/2 ∈ L`.
3. If moreover `L ⊆ Z^m` and `x ≠ y`, then `∥x − y∥2 ≥ 2`.

**Formalization Note.** `c ∈ {0,1}ⁿ` is `c : Fin n → Fin 2`, read in `ℝ`. `L ⊆ Z^m` is the hypothesis that every
lattice vector has integer coordinates. -/
theorem fact_2_7 {m n : ℕ} (B : Matrix (Fin m) (Fin n) ℝ) (hB : LinearIndependent ℝ B.transpose) :
    ((∀ c : Fin n → Fin 2, twoLPlus B (B.mulVec fun i => ((c i : ℕ) : ℝ)) ⊆ latt B) ∧
      ∀ x ∈ latt B, ∃! c : Fin n → Fin 2, x ∈ twoLPlus B (B.mulVec fun i => ((c i : ℕ) : ℝ))) ∧
    (∀ (c : Fin n → Fin 2) (x y : Fin m → ℝ),
      x ∈ twoLPlus B (B.mulVec fun i => ((c i : ℕ) : ℝ)) →
      y ∈ twoLPlus B (B.mulVec fun i => ((c i : ℕ) : ℝ)) →
      (1 / 2 : ℝ) • (x + y) ∈ latt B) ∧
    ((∀ x ∈ latt B, ∀ j, ∃ k : ℤ, x j = k) →
      ∀ (c : Fin n → Fin 2) (x y : Fin m → ℝ),
        x ∈ twoLPlus B (B.mulVec fun i => ((c i : ℕ) : ℝ)) →
        y ∈ twoLPlus B (B.mulVec fun i => ((c i : ℕ) : ℝ)) → x ≠ y →
        2 ≤ l2Norm (x - y)) := by sorry

end SpikyCVP
