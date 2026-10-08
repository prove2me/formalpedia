-- Prove2me | Theorems.Thm_SelfDualLP_Complexity_theorem_6_data
-- name    : SelfDualLP.Complexity.theorem_6_data
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:58:39.637063+00:00
-- url     : https://prove2.me/theorems/f235a1d7-faa7-44c5-ba4b-18393beaf150
-- title:
--   Theorem 6, first sentence — the data of (HLP) remain integral with bit length $O(L)$
-- statement:
--   Let $A\in\mathbb Z^{m\times n}$, $b\in\mathbb Z^m$, $c\in\mathbb Z^n$ be integer data with $n\ge1$ and bit length $L$. Under the choice (7) the additional data of (HLP),
--   $$
--   \bar b=b-Ae,\qquad \bar c=c-e,\qquad \bar z=c^Te+1,
--   $$
--   are integral, and the bit length of all the (HLP) data ($A,b,c,\bar b,\bar c,\bar z$ and the right-hand side $-(n+1)$) is $O(L)$: at most $C\cdot L$ for an absolute constant $C>0$.
--
--   This is why the complexity bound for (HLP) is stated in terms of the bit length $L$ of the original data.
--
--   **Formalization Note** Integrality is stated as: the real vectors $\bar b,\bar c$ and the real number $\bar z$ obtained from the cast data are the casts of the corresponding integer expressions. $O(L)$ is pinned with $C$ chosen before $m,n,A,b,c$. The paper implicitly has $n\ge1$; this excludes an empty LP whose input length is zero while (HLP) still has a nonzero normalizing constant.
-- source:
--   Ye, Todd, Mizuno, An O(√nL)-Iteration Homogeneous and Self-Dual Linear Programming Algorithm, Math. Oper. Res. 19(1) (1994), p. 61, Theorem 6 (first sentence); (8) on p. 58

import Mathlib
import Definitions.Def_SelfDualLP_Complexity_HLP
import Definitions.Def_SelfDualLP_Complexity_BitLength

open Matrix

namespace SelfDualLP.Complexity

/-- Theorem 6, first sentence (p. 61). For integer data `(A, b, c)` with `n ≥ 1` and bit length `L`, the data
of (HLP) under (7) remain integral — `b̄ = b − Ae`, `c̄ = c − e`, `z̄ = cᵀe + 1` are the casts of
the integer vectors/number `bbarInt`, `cbarInt`, `zbarInt` — and the bit length of the (HLP)
data is `O(L)`: at most `C·L` for an absolute constant `C`. -/
theorem theorem_6_data :
    ∃ C : ℝ, 0 < C ∧ ∀ (m n : ℕ), 1 ≤ n →
      ∀ (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (c : Fin n → ℤ),
      bbar (castMat A) (castVec b) (ones n) = castVec (bbarInt A b) ∧
      cbar (castMat A) (castVec c) 0 (ones n) = castVec (cbarInt c) ∧
      zbar (castVec b) (castVec c) (ones n) 0 = ((zbarInt c : ℤ) : ℝ) ∧
      (hlpBitLength A b c : ℝ) ≤ C * (bitLength A b c : ℝ) := by sorry

end SelfDualLP.Complexity
