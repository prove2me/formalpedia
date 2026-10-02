-- Prove2me | Theorems.Thm_TeschlQM_Algebraic_ladder_commutator
-- name    : TeschlQM.Algebraic.ladder_commutator
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T02:27:20.265577+00:00
-- url     : https://prove2.me/theorems/62fc348e-4558-4115-9960-d7b08061c6a7
-- title:
--   Eq. (8.36) — the commutation relation [A₋, A₊] = 1 on 𝔇_ω
-- statement:
--   Let $\omega > 0$ and let $A_\pm$ be the ladder operators on $\mathfrak D_\omega = \operatorname{span}\{x^k e^{-\omega x^2/2}\}$ (functions $\mathbb R \to \mathbb C$). Then for every $f \in \mathfrak D_\omega$
--   $$[A_-, A_+] f = A_-(A_+ f) - A_+(A_- f) = f.$$
--
--   This canonical commutation relation is what makes $A_+$ raise and $A_-$ lower the eigenvalues of $N = A_+A_-$ by one.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 178, Eq. (8.36)

import Mathlib
import Definitions.Def_TeschlQM_Algebraic_ladder

namespace TeschlQM.Algebraic

/-- Teschl, Eq. (8.36), p. 178: for `ω > 0` the ladder operators (8.35) satisfy the canonical
commutation relation `[A₋, A₊] = A₋A₊ − A₊A₋ = 1` on `𝔇_ω`. -/
theorem ladder_commutator (ω : ℝ) (hω : 0 < ω) (f : ℝ → ℂ) (hf : f ∈ core1 ω) :
    ladderMinus ω (ladderPlus ω f) - ladderPlus ω (ladderMinus ω f) = f := by sorry

end TeschlQM.Algebraic
