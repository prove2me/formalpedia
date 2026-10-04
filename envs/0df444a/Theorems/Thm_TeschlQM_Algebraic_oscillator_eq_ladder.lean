-- Prove2me | Theorems.Thm_TeschlQM_Algebraic_oscillator_eq_ladder
-- name    : TeschlQM.Algebraic.oscillator_eq_ladder
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T02:38:59.66239+00:00
-- url     : https://prove2.me/theorems/b753eb34-d60a-411b-ae9b-56030e338b38
-- title:
--   Eq. (8.37) — H = ω(2N + 1), N = A₊A₋, on 𝔇_ω, and 𝔇_ω is invariant under A±
-- statement:
--   Let $\omega > 0$, and let $A_\pm$ be the ladder operators on $\mathfrak D_\omega = \operatorname{span}\{x^k e^{-\omega x^2/2}\}$. For every $f \in \mathfrak D_\omega$ the one-dimensional harmonic oscillator $H = -\frac{d^2}{dx^2} + \omega^2 x^2$ satisfies
--   $$-f'' + \omega^2 x^2 f = \omega\,(2 A_+ A_- f + f), \qquad \text{i.e. } H = \omega(2N + 1),\ N = A_+A_-,$$
--   and $A_+ f,\ A_- f \in \mathfrak D_\omega$.
--
--   The factorization reduces the spectral problem for $H$ to that of the number operator $N$.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 178, Eq. (8.37)

import Mathlib
import Definitions.Def_TeschlQM_Algebraic_ladder

namespace TeschlQM.Algebraic

/-- Teschl, Eq. (8.37), p. 178: for `ω > 0`, on every function `f ∈ 𝔇_ω` the one-dimensional
harmonic oscillator `H = −d²/dx² + ω²x²` equals `ω(2N + 1)` with `N = A₊A₋`; moreover `𝔇_ω` is
invariant under `A₊` and `A₋`. -/
theorem oscillator_eq_ladder (ω : ℝ) (hω : 0 < ω) :
    (∀ f ∈ core1 ω,
      (fun x : ℝ => -deriv (deriv f) x + ((ω ^ 2 * x ^ 2 : ℝ) : ℂ) * f x) =
        fun x : ℝ => (ω : ℂ) * (2 * ladderPlus ω (ladderMinus ω f) x + f x)) ∧
      (∀ f ∈ core1 ω, ladderPlus ω f ∈ core1 ω ∧ ladderMinus ω f ∈ core1 ω) := by sorry

end TeschlQM.Algebraic
