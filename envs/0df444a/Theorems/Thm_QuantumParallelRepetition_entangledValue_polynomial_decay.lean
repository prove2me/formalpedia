-- Prove2me | Theorems.Thm_QuantumParallelRepetition_entangledValue_polynomial_decay
-- name    : QuantumParallelRepetition.entangledValue_polynomial_decay
-- status  : Proved
-- author  : @Henry Yuen
-- created : 2026-08-09T03:16:39.041033+00:00
-- url     : https://prove2.me/theorems/48391107-25ae-4fa0-a4d2-51b0c8be9504
-- statement:
--   Let $G$ be a finite two-player one-round game with nonempty answer alphabets and entangled value $\omega^*(G)<1$. Then there are constants $C>0$ and $\alpha>0$, depending only on $G$, such that every positive repetition count $m$ satisfies
--
--   $$
--   \omega^*(G^m)\le C m^{-\alpha}.
--   $$
--
--   Thus the repeated value not only tends to zero but admits an inverse-polynomial upper bound. This is the quantitative decay supplied by Yuen's parallel-repetition theorem, stated abstractly without fixing the exponent or the dependence of the constants on the game.
--
--   **Formalization Note** The Lean theorem writes $m=n+1$ so that the real power has a strictly positive base and the estimate begins at the one-fold repetition.
-- source:
--   Henry Yuen, A parallel repetition theorem for all entangled games, arXiv:1604.04340v1, p. 2, Theorem 1 (Main Theorem), https://arxiv.org/abs/1604.04340

import Definitions.Def_quantum_parallel_repetition_game
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace QuantumParallelRepetition

/-- The entangled value of a nontrivial finite game decays at least polynomially
under parallel repetition.  The constants may depend on the game. -/
theorem entangledValue_polynomial_decay
    {X Y A B : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B]
    (G : Game X Y A B)
    (hG : entangledValue G < 1) :
    ∃ C α : ℝ, 0 < C ∧ 0 < α ∧ ∀ n : ℕ,
      repeatedEntangledValue G (n + 1) ≤ C * Real.rpow (n + 1) (-α) := by
  sorry

end QuantumParallelRepetition
