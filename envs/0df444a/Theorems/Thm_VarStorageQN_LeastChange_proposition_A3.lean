-- Prove2me | Theorems.Thm_VarStorageQN_LeastChange_proposition_A3
-- name    : VarStorageQN.LeastChange.proposition_A3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:46:31.675024+00:00
-- url     : https://prove2.me/theorems/c4d0069e-a1ac-4d87-a3e5-2ceb759cb10d
-- title:
--   Proposition A.3 — existence of positive self-adjoint secant operators
-- statement:
--   Let $y$ and $s$ be two nonzero vectors in a real Hilbert space $\mathcal H$. The following are equivalent:
--
--   1. there is a self-adjoint, positive $B\in L(\mathcal H)$ with $y=Bs$;
--   2. there is a bijective $C\in L(\mathcal H)$ with $y=C^*Cs$;
--   3. $\langle y,s\rangle>0$.
--
--   Here "positive" means $\langle Bu,u\rangle>0$ for every $u\ne0$ (§2.1). The proposition answers when the secant equation (A.3) admits a positive self-adjoint solution, and condition 2 supplies the weight $R=C^{-1}$ that turns (A.7) into the dfp formula (A.8).
--
--   **Formalization Note** Positivity is the strict predicate `IsPositiveStrict`. A bijective bounded operator is a continuous linear equivalence $C:\mathcal H\simeq\mathcal H$; by the bounded inverse theorem this is the same as a bijective element of $L(\mathcal H)$.
-- source:
--   Gilbert & Lemaréchal, Some numerical experiments with variable-storage quasi-Newton algorithms, IIASA Working Paper WP-88-121 (August 1988), p. 29, Proposition A.3

import Mathlib
import Definitions.Def_VarStorageQN_LeastChange_Bracket

namespace VarStorageQN.LeastChange

open InnerProductSpace ContinuousLinearMap
open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Proposition A.3, p. 29: for nonzero `y, s`, a self-adjoint (strictly) positive secant
operator exists iff `y = C*Cs` for a bijective `C` iff `⟨y,s⟩ > 0`. -/
theorem proposition_A3 (y s : H) (hy : y ≠ 0) (hs : s ≠ 0) :
    List.TFAE
      [∃ B : H →L[ℝ] H, IsSelfAdjoint B ∧ IsPositiveStrict B ∧ y = B s,
       ∃ C : H ≃L[ℝ] H, y = adjoint (C : H →L[ℝ] H) (C s),
       0 < ⟪y, s⟫_ℝ] := by sorry

end VarStorageQN.LeastChange
