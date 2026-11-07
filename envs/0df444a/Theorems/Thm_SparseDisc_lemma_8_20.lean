-- Prove2me | Theorems.Thm_SparseDisc_lemma_8_20
-- name    : SparseDisc.lemma_8_20
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:54:38.533632+00:00
-- url     : https://prove2.me/theorems/e1c3b10d-90f2-4687-9824-0f24e8eefd8a
-- title:
--   Lemma 8.20 — an asymmetric version of $K_2 = 2$
-- statement:
--   1. For any odd 2-Lipschitz functions $\varphi, \psi$ on $\{\pm1\}^{[m]}$ there is $x$ with $|\varphi(x)| \le 1$ and $|\psi(x)| \le 2$.
--   2. Consequently every 1-coarse set contains a 2-loop.
--   3. If $\ell_1, \ell_2 \ge 1$ with $\max(\ell_1, \ell_2) \ge 2$, every $\ell_1$-coarse set contains an $\ell_2$-loop.
--
--   The lemma handles constraints at level 1 in the leveled deletions of Section 8.6.
--
--   **Formalization Note** The item sets are arbitrary finite types, including the empty one (for which the claims are trivial, as noted on p.37); $\ell_1, \ell_2$ are real.
--
--   Differences from the source:
--   - encoding: the item set [m] → a finite type of items; reason: Lean convention; [m] is the case Fin m, and every finite set is in bijection with some [m]
-- source:
--   Zeng–Cao–Dai–Wang–Liao, Sparse Discrepancy Beyond Additive Functions: Acyclic, Bounded-Degree and Degenerate Sparsity Patterns, STOC 2027 submission (manuscript sha256 0f09ec60…25b81), Lemma 8.20, p.37

import Mathlib
import Definitions.Def_SparseDisc_IsOdd
import Definitions.Def_SparseDisc_IsLip
import Definitions.Def_SparseDisc_IsCoarse
import Definitions.Def_SparseDisc_HasLoop

namespace SparseDisc

/-- **Lemma 8.20** (Zeng–Cao–Dai–Wang–Liao, *Sparse Discrepancy Beyond Additive Functions*, STOC
2027 submission manuscript (sha256 0f09ec60…25b81), p.37). For any odd 2-Lipschitz `φ, ψ` on
`{±1}^[m]` there is `x` with `|φ(x)| ≤ 1` and `|ψ(x)| ≤ 2`. Consequently every 1-coarse set
contains a 2-loop, and if `ℓ₁, ℓ₂ ≥ 1` with `max(ℓ₁, ℓ₂) ≥ 2`, every `ℓ₁`-coarse set contains an
`ℓ₂`-loop.

**Formalization Note** `[m]` and the cube of the coarse set are arbitrary finite types (the empty
type included, as in Section 8.1); `ℓ₁, ℓ₂` are real. -/
theorem lemma_8_20 :
    (∀ (ι : Type) [Fintype ι] (φ ψ : Cube ι → ℝ), IsOdd φ → IsLip 2 φ → IsOdd ψ → IsLip 2 ψ →
      ∃ x : Cube ι, |φ x| ≤ 1 ∧ |ψ x| ≤ 2) ∧
    (∀ (U : Type) [Fintype U] (Z : Set (Cube U)), IsCoarse 1 Z → HasLoop 2 Z) ∧
    (∀ (U : Type) [Fintype U] (Z : Set (Cube U)) (ℓ₁ ℓ₂ : ℝ), 1 ≤ ℓ₁ → 1 ≤ ℓ₂ →
      2 ≤ max ℓ₁ ℓ₂ → IsCoarse ℓ₁ Z → HasLoop ℓ₂ Z) := by sorry

end SparseDisc
