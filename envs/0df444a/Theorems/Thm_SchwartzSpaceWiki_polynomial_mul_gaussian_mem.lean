-- Prove2me | Theorems.Thm_SchwartzSpaceWiki_polynomial_mul_gaussian_mem
-- name    : SchwartzSpaceWiki.polynomial_mul_gaussian_mem
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-13T00:15:22.356732+00:00
-- url     : https://prove2.me/theorems/4fd15f7c-6984-441f-99bb-6b541060ba48
-- title:
--   $P(x)e^{-a|x|^2}\in\mathcal{S}(\mathbb{R}^n)$ and polynomials embed
-- statement:
--   Fix a real number $a>0$. For every polynomial $P\in\mathbb{C}[x_1,\dots,x_n]$, the function $x\mapsto P(x)\,e^{-a|x|^2}$ belongs to $\mathcal{S}(\mathbb{R}^n)$. Moreover, the map $P\mapsto P(x)e^{-a|x|^2}$ from polynomials to functions is injective, so it embeds the polynomials into $\mathcal{S}(\mathbb{R}^n)$.
-- source:
--   Wikipedia, "Schwartz space", revision oldid=1360762580 (https://en.wikipedia.org/w/index.php?title=Schwartz_space&oldid=1360762580), section "Examples of functions in the Schwartz space", 3rd bullet

import Mathlib
import Definitions.Def_SchwartzSpaceWiki_Defs

open MeasureTheory

namespace SchwartzSpaceWiki

theorem polynomial_mul_gaussian_mem (n : ℕ) (a : ℝ) (ha : 0 < a) :
    (∀ P : MvPolynomial (Fin n) ℂ,
      (fun x : Rn n => MvPolynomial.eval (fun i => (x i : ℂ)) P *
        Complex.exp (-(a * ‖x‖ ^ 2 : ℝ))) ∈ schwartzSpace n) ∧
    Function.Injective (fun (P : MvPolynomial (Fin n) ℂ) (x : Rn n) =>
      MvPolynomial.eval (fun i => (x i : ℂ)) P * Complex.exp (-(a * ‖x‖ ^ 2 : ℝ))) := by sorry

end SchwartzSpaceWiki
