-- Prove2me | Theorems.Thm_TeschlQM_Algebraic_hermite_functions
-- name    : TeschlQM.Algebraic.hermite_functions
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T02:51:03.986293+00:00
-- url     : https://prove2.me/theorems/2097b209-6408-45b8-abba-a5f98e81eb41
-- title:
--   Eqs. (8.40)–(8.42) — ψₙ = A₊ⁿψ₀/√n! are the Hermite functions, normalized eigenfunctions of N spanning 𝔇_ω
-- statement:
--   Let $\omega > 0$ and $\psi_0(x) = (\omega/\pi)^{1/4} e^{-\omega x^2/2}$. Then for every $n \in \mathbb N_0$
--   $$\frac{1}{\sqrt{n!}} A_+^n \psi_0 = \psi_n, \qquad \psi_n(x) = \frac{1}{\sqrt{2^n n!}}\Big(\frac{\omega}{\pi}\Big)^{1/4} H_n(\sqrt\omega\,x)\,e^{-\omega x^2/2},$$
--   with $H_n$ the Hermite polynomials $H_n(x) = (-1)^n e^{x^2}\frac{d^n}{dx^n}e^{-x^2}$. Moreover $\psi_n \in \mathfrak D_\omega$, $A_+A_-\psi_n = n\,\psi_n$, $\int_{\mathbb R} |\psi_n(x)|^2\,dx = 1$, and
--   $$\operatorname{span}\{\psi_n \mid n \in \mathbb N_0\} = \mathfrak D_\omega = \operatorname{span}\{x^k e^{-\omega x^2/2} \mid k \in \mathbb N_0\}.$$
--
--   These one-dimensional facts give, by taking products, the eigenbasis of the three-dimensional oscillator.
--
--   **Formalization Note.** $A_+^n$ is the $n$-fold iterate of `ladderPlus ω`. The normalization is stated as integrability of $|\psi_n|^2$ together with $\int |\psi_n|^2 = 1$.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, pp. 178–179, Eqs. (8.39)–(8.42)

import Mathlib
import Definitions.Def_TeschlQM_Algebraic_ladder
import Definitions.Def_TeschlQM_Algebraic_hermiteFunction

namespace TeschlQM.Algebraic

open MeasureTheory

/-- Teschl, Eqs. (8.39)–(8.42), pp. 178–179: for `ω > 0`, with the ground state
`ψ₀(x) = (ω/π)^{1/4} e^{−ωx²/2}` (8.39):
* `ψₙ = (1/√n!) A₊ⁿ ψ₀` (8.40) is the Hermite function
  `(2ⁿ n!)^{−1/2} (ω/π)^{1/4} Hₙ(√ω x) e^{−ωx²/2}` of (8.41), with `Hₙ` from (8.42);
* `ψₙ` is a normalized eigenfunction of `N = A₊A₋` for the eigenvalue `n`:
  `ψₙ ∈ 𝔇_ω`, `A₊A₋ψₙ = nψₙ`, `∫ |ψₙ|² = 1`;
* `span{ψₙ | n ∈ ℕ₀} = 𝔇_ω = span{xᵏ e^{−ωx²/2} | k ∈ ℕ₀}`. -/
theorem hermite_functions (ω : ℝ) (hω : 0 < ω) :
    (∀ n : ℕ,
      (fun x : ℝ => ((1 / Real.sqrt n.factorial : ℝ) : ℂ) *
          (ladderPlus ω)^[n]
            (fun y : ℝ => (((ω / Real.pi) ^ (1 / 4 : ℝ) * Real.exp (-(ω * y ^ 2) / 2) : ℝ) : ℂ))
            x) =
        hermiteFunction ω n) ∧
      (∀ n : ℕ, hermiteFunction ω n ∈ core1 ω ∧
        ladderPlus ω (ladderMinus ω (hermiteFunction ω n)) = (n : ℂ) • hermiteFunction ω n ∧
        Integrable (fun x : ℝ => ‖hermiteFunction ω n x‖ ^ 2) ∧
        ∫ x : ℝ, ‖hermiteFunction ω n x‖ ^ 2 = 1) ∧
      Submodule.span ℂ (Set.range (hermiteFunction ω)) = core1 ω := by sorry

end TeschlQM.Algebraic
