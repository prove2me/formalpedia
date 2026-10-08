-- Prove2me | Theorems.Thm_SelfDualLP_Complexity_theorem_6
-- name    : SelfDualLP.Complexity.theorem_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T18:01:20.191198+00:00
-- url     : https://prove2.me/theorems/c60d9213-3017-4788-a751-a56ef2be2e8b
-- title:
--   Theorem 6 — a strictly self-complementary solution of (HLP) in $O(\sqrt n L)$ predictor–corrector iterations
-- statement:
--   Let (LP) and (LD) have integer data $A\in\mathbb Z^{m\times n}$, $b\in\mathbb Z^m$, $c\in\mathbb Z^n$ with $n\ge1$ and bit length $L$. There is an absolute constant $C>0$ such that there is a finite predictor–corrector run under the choice (7) ending at an iteration
--   $$
--   k\le C\sqrt n\,L
--   $$
--   at which the termination projection has an output, and every termination output at $z^k$, rescaled to the normalization (9), is a strictly self-complementary solution of (HLP).
--
--   That is, the predictor–corrector algorithm, coupled with the termination technique, generates a strictly self-complementary solution for (HLP) in $O(\sqrt nL)$ iterations.
--
--   **Formalization Note** $O(\sqrt nL)$ is pinned as $C\sqrt n\,L$ with $C$ absolute, chosen before $m,n$ and the data. The algorithm is a relation on finite runs: a Newton solution and the attained predictor maximum are required for steps before the termination iterate. Existence of a successful finite run is asserted, so the theorem remains substantive when an infinite run cannot be extended. The hypothesis $n\ge1$ is implicit in the paper. The rescaling by $(n+1)/(e^Tx^*+e^Ts^*+\tau^*+\kappa^*)$ is needed because the projection imposes only the homogeneous rows of (HLP).
-- source:
--   Ye, Todd, Mizuno, An O(√nL)-Iteration Homogeneous and Self-Dual Linear Programming Algorithm, Math. Oper. Res. 19(1) (1994), p. 61, Theorem 6; proof on pp. 61–62

import Mathlib
import Definitions.Def_SelfDualLP_Complexity_LPData
import Definitions.Def_SelfDualLP_Complexity_HLP
import Definitions.Def_SelfDualLP_Complexity_Neighborhood
import Definitions.Def_SelfDualLP_Complexity_PCSequence
import Definitions.Def_SelfDualLP_Complexity_Termination
import Definitions.Def_SelfDualLP_Complexity_BitLength

open Matrix

namespace SelfDualLP.Complexity

/-- Theorem 6 (p. 61), with `O(√n L)` pinned as `C·√n·L` for an absolute constant `C > 0`. Let
(LP) and (LD) have integer data `(A, b, c)` with `n ≥ 1` and bit length `L`. For every sequence of
iterates of the predictor–corrector algorithm applied to (HLP) under (7), there is a finite
run ending at iteration `k ≤ C√n L` at which the termination projection has an output, and every termination
output at `zᵏ`, rescaled to (9), is a strictly self-complementary solution of (HLP). -/
theorem theorem_6 :
    ∃ C : ℝ, 0 < C ∧ ∀ (m n : ℕ), 1 ≤ n →
      ∀ (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (c : Fin n → ℤ),
        ∃ (k : ℕ) (z : ℕ → HLPPoint m n),
          IsPCSequence (castMat A) (castVec b) (castVec c) z k ∧
          (k : ℝ) ≤ C * Real.sqrt (n : ℝ) * (bitLength A b c : ℝ) ∧
          (∃ u, IsTerminationOutput (castMat A) (castVec b) (castVec c) (z k) u) ∧
          ∀ u, IsTerminationOutput (castMat A) (castVec b) (castVec c) (z k) u →
            StrictlySelfComplementary7 (castMat A) (castVec b) (castVec c) (rescaleOutput u) := by sorry

end SelfDualLP.Complexity
