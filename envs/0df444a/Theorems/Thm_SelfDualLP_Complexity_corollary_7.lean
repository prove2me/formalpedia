-- Prove2me | Theorems.Thm_SelfDualLP_Complexity_corollary_7
-- name    : SelfDualLP.Complexity.corollary_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T18:01:59.870991+00:00
-- url     : https://prove2.me/theorems/270f2c7e-bf21-4905-bee2-4e90a61a1500
-- title:
--   Corollary 7 — within $O(\sqrt n L)$ iterations the algorithm finds optimal solutions of (LP) and (LD) or detects infeasibility
-- statement:
--   Let (LP) $\min\{c^Tx: Ax=b,\ x\ge0\}$ and (LD) $\max\{b^Ty: A^Ty\le c\}$ have integer data $A\in\mathbb Z^{m\times n}$, $b\in\mathbb Z^m$, $c\in\mathbb Z^n$ with $n\ge1$ and bit length $L$. There is an absolute constant $C>0$ such that there is a finite predictor–corrector run under the choice (7) ending at an iteration
--   $$
--   k\le C\sqrt n\,L
--   $$
--   at which the termination projection has an output, and every termination output $u=(y^*,x^*,\tau^*,\theta^*,s^*,\kappa^*)$ at $z^k$ satisfies one of:
--
--   1. $\tau^*>0$, $x^*/\tau^*$ is an optimal solution of (LP) and $(y^*/\tau^*,\,s^*/\tau^*)$ is an optimal solution of (LD);
--   2. $\tau^*=0$ and the output indicates infeasibility: either $c^Tx^*<0$ and (LD) is infeasible, or $-b^Ty^*<0$ and (LP) is infeasible.
--
--   In words: within $O(\sqrt nL)$ iterations, the predictor–corrector algorithm, coupled with the termination technique, generates either optimal solutions to (LP) and (LD) or an indication that (LP) or (LD) is infeasible.
--
--   **Formalization Note** $O(\sqrt nL)$ is pinned as $C\sqrt n\,L$ with $C$ absolute, chosen before $m,n$ and the data; $L$ is the encoding size of the integer data (definition BitLength) and $n\ge1$ is implicit in the paper. "An indication that (LP) or (LD) is infeasible" is read through Theorem 3 (ii): the indication is the negative sign of $c^Tx^*$ or $-b^Ty^*$ together with the infeasibility it certifies. The conclusions are stated for the unscaled projection output; they are invariant under the positive rescaling to (9). The algorithm is a relation on finite runs: a Newton solution and the attained predictor maximum are required for steps before the termination iterate. Existence of a successful finite run is asserted, so the corollary remains substantive when an infinite run cannot be extended.
-- source:
--   Ye, Todd, Mizuno, An O(√nL)-Iteration Homogeneous and Self-Dual Linear Programming Algorithm, Math. Oper. Res. 19(1) (1994), p. 62, Corollary 7; Theorem 6 (p. 61) and Theorem 3 (p. 58)

import Mathlib
import Definitions.Def_SelfDualLP_Complexity_LPData
import Definitions.Def_SelfDualLP_Complexity_HLP
import Definitions.Def_SelfDualLP_Complexity_Neighborhood
import Definitions.Def_SelfDualLP_Complexity_PCSequence
import Definitions.Def_SelfDualLP_Complexity_Termination
import Definitions.Def_SelfDualLP_Complexity_BitLength

open Matrix

namespace SelfDualLP.Complexity

/-- Corollary 7 (p. 62), with `O(√n L)` pinned as `C·√n·L` for an absolute constant `C > 0`.
Let (LP) and (LD) have integer data `(A, b, c)` with `n ≥ 1` and bit length `L`. For every
finite run of the predictor–corrector algorithm applied to (HLP) under (7), there
is an iteration `k ≤ C√n L` at which the termination projection has an output, and every
termination output `u = (y*, x*, τ*, θ*, s*, κ*)` at `zᵏ` either
* has `τ* > 0`, `x*/τ*` optimal for (LP) and `(y*/τ*, s*/τ*)` optimal for (LD), or
* has `τ* = 0` and indicates infeasibility: `cᵀx* < 0` and (LD) is infeasible, or
  `−bᵀy* < 0` and (LP) is infeasible. -/
theorem corollary_7 :
    ∃ C : ℝ, 0 < C ∧ ∀ (m n : ℕ), 1 ≤ n →
      ∀ (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (c : Fin n → ℤ),
        ∃ (k : ℕ) (z : ℕ → HLPPoint m n),
          IsPCSequence (castMat A) (castVec b) (castVec c) z k ∧
          (k : ℝ) ≤ C * Real.sqrt (n : ℝ) * (bitLength A b c : ℝ) ∧
          (∃ u, IsTerminationOutput (castMat A) (castVec b) (castVec c) (z k) u) ∧
          ∀ u, IsTerminationOutput (castMat A) (castVec b) (castVec c) (z k) u →
            (0 < u.τ ∧ LPOptimal (castMat A) (castVec b) (castVec c) (u.τ⁻¹ • u.x) ∧
                LDOptimal (castMat A) (castVec b) (castVec c) (u.τ⁻¹ • u.y) (u.τ⁻¹ • u.s)) ∨
            (u.τ = 0 ∧
              ((castVec c ⬝ᵥ u.x < 0 ∧ ¬ LDIsFeasible (castMat A) (castVec c)) ∨
               (-(castVec b ⬝ᵥ u.y) < 0 ∧ ¬ LPIsFeasible (castMat A) (castVec b) (castVec c)))) := by sorry

end SelfDualLP.Complexity
