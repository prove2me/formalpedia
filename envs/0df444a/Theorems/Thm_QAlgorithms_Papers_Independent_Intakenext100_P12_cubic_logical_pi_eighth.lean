-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P12_cubic_logical_pi_eighth
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P12.cubic_logical_pi_eighth
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:13:20.076848+00:00
-- url     : https://prove2.me/theorems/0d6e0fcd-1e64-4b25-8712-9a8a8ea44a87
-- title:
--   §XI.B (120)–(123): cubic polynomial realizes logical pi/8
-- statement:
--   Let $\alpha>0$ and use the nonzero two-dimensional ideal square comb encoder $J$. Its Schwartz realization is continuous and injective. The polynomial-phase multiplier
--
--   $$W(q)=\exp\!\left[\frac{i\pi}{4}\left(2(q/\alpha)^3+(q/\alpha)^2-2q/\alpha\right)\right]$$
--
--   preserves the code and induces $\operatorname{diag}(1,e^{i\pi/4})$, equivalent to the paper's $S$ up to a scalar phase. For every integer $x$, the integer polynomial $2x^3+x^2-2x$ is $0\bmod8$ for even $x$ and $1\bmod8$ for odd $x$. The multiplier factors as the cubic gate $e^{i\gamma q^3}$, $\gamma=\pi/(2\alpha^3)$, times the displayed quadratic/linear phase.
--
--   This is the source's cubic construction, not an assertion about an unrelated quartic multiplier.
-- source:
--   Encoding a qubit in an oscillator, arXiv:quant-ph/0008040v3, PDF p. 16, §XI.B (120)–(123): cubic polynomial realizes logical pi/8

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P12

noncomputable section

open scoped BigOperators

open MeasureTheory Matrix ComplexConjugate

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase sigma)

namespace QAlgorithms.Papers.Independent.Intakenext100.P12

/-- Section XI.B (120)–(123), PDF p.16: the cubic-plus-quadratic multiplier implements T,
equivalently the paper's S up to global phase. The ideal code realization is nonzero and injective. -/
theorem cubic_logical_pi_eighth (alpha : ℝ) (ha : 0 < alpha) :
    (∀ j : Fin 2, ∀ k : ℤ,
      (2 * ((j.val : ℤ) + 2 * k) ^ 3 + ((j.val : ℤ) + 2 * k) ^ 2 -
        2 * ((j.val : ℤ) + 2 * k)) % 8 = j.val) ∧
    Function.Injective (idealComb 2 alpha) ∧
    (∀ c : Fin 2 → ℂ, ∃ T : SchwartzMap ℝ ℂ →L[ℂ] ℂ,
      ∀ f, T f = idealComb 2 alpha c f) ∧
    (∀ c : Fin 2 → ℂ, ∀ f : SchwartzMap ℝ ℂ,
      phasedComb 2 alpha c (cubicLogicalPhase alpha) f =
        idealComb 2 alpha (fun j => cisPhase (Real.pi * j.val / 4) * c j) f) ∧
    (∀ q : ℝ, cisPhase (cubicLogicalPhase alpha q) =
      cisPhase (Real.pi / (2 * alpha ^ 3) * q ^ 3) *
        cisPhase (Real.pi / 4 * ((q / alpha) ^ 2 - 2 * q / alpha))) ∧
    (∀ j : Fin 2, ∀ s : ℤ,
      cisPhase (cubicLogicalPhase alpha (combSupportPoint 2 alpha j s)) = cisPhase (Real.pi * j.val / 4)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P12

end
