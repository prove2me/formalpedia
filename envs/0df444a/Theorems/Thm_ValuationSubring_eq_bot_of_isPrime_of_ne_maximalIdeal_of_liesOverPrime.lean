-- Prove2me | Theorems.Thm_ValuationSubring_eq_bot_of_isPrime_of_ne_maximalIdeal_of_liesOverPrime
-- name    : ValuationSubring.eq_bot_of_isPrime_of_ne_maximalIdeal_of_liesOverPrime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/2802c4b0-958a-57f7-9192-c5febfe4da98
-- title:
--   Valuation subrings of ℚ̄ over p have rank one
-- statement:
--   Let $p$ be a prime number and let $A$ be a valuation subring of the algebraic closure $\overline{\mathbb Q}$ of $\mathbb Q$ which lies over $p$ in the sense that the image of $p$ in $\overline{\mathbb Q}$ belongs to the set of non-units of $A$, i.e. $p$ is a non-invertible element of $A$. Let $\mathfrak q$ be an ideal of $A$ which is prime, and suppose that $\mathfrak q$ is distinct from the maximal ideal of $A$ (as the local ring $A$ is, $A$ being a valuation subring of a field). The conclusion is that $\mathfrak q$ is the zero ideal. Equivalently: the only prime ideals of such an $A$ are $(0)$ and the maximal ideal, so $A$ has Krull dimension at most one and $\operatorname{Spec} A$ has at most two points.
--
--   This is the statement that a valuation subring of $\overline{\mathbb Q}$ lying above a rational prime has rank one, so that its spectrum consists only of the generic point and the closed point. It is used repeatedly in the analysis of fibres of models over such valuation rings, for instance in the arguments about places and branches on the models of modular curves that invoke a dichotomy between the generic and the special fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_eq_bot_of_isPrime_of_ne_maximalIdeal_of_liesOverPrime.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ValuationSubring.eq_bot_of_isPrime_of_ne_maximalIdeal_of_liesOverPrime
    {p : ℕ} (hp : p.Prime) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (𝔮 : Ideal ↥A) [𝔮.IsPrime] (h𝔮 : 𝔮 ≠ IsLocalRing.maximalIdeal ↥A) : 𝔮 = ⊥ := by sorry
