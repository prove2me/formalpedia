-- Prove2me | Theorems.Thm_UnphysicalHilbert_change_of_coordinates_finite_to_infinite_expectation
-- name    : UnphysicalHilbert.change_of_coordinates_finite_to_infinite_expectation
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T21:10:20.370842+00:00
-- url     : https://prove2.me/theorems/03f2a0dc-30f3-4543-ab57-ee45ade18015
-- title:
--   Goal — a change of coordinates on $L^2(\mathbb R)$ turns a finite expectation into an infinite one
-- statement:
--   There exist an orientation-preserving diffeomorphism $f:\mathbb R\to\mathbb R$ (with $f$, $f^{-1}$ smooth and $f$ strictly increasing), a unitary operator $U$ on $L^2(\mathbb R;\mathbb C)$ acting by the change of variables
--   $$(Ug)(y)=g\bigl(f^{-1}(y)\bigr)\sqrt{\bigl|(f^{-1})'(y)\bigr|}\quad\text{for a.e. }y,\ \text{for every }g\in L^2(\mathbb R),$$
--   and a state $\psi\in L^2(\mathbb R)$ with $\|\psi\|_2=1$, such that
--   $$\int_{\mathbb R}|x|^n\,|\psi(x)|^2\,dx<\infty\quad\text{for every }n\in\mathbb N,\qquad\text{but}\qquad\int_{\mathbb R}y^2\,|(U\psi)(y)|^2\,dy=\infty .$$
--
--   In words: a unitary transformation of $L^2(\mathbb R)$ coming from a mere change of the position coordinate maps a state whose position moments are all finite to a state with infinite expected squared position. This is the mathematical content of the paper's claim that completeness forces "coordinate transformations that take finite expectations to infinite ones" (and, applying $U^{-1}$, vice versa).
--
--   **Formalization Note** The paper's witnesses are $f(x)=\tan(\frac\pi2\operatorname{erf}x)$ and the Gaussian state of eq. (27), but the goal only asserts existence. Finiteness and infiniteness of the moment integrals are expressed via Lebesgue integrability.
-- source:
--   G. Carcassi, C. A. Aidala, F. Calderón, *The unphysicality of Hilbert spaces*, arXiv:2308.06669v3 [quant-ph], 22 Dec 2024, https://arxiv.org/abs/2308.06669, Section VI, pp. 10–12 (Proposition 24, eqs. (26)–(29)); abstract

import Definitions.Def_UnphysicalHilbert_Position

namespace UnphysicalHilbert

open MeasureTheory

/-- Goal: in `L²(ℝ)` there is a unitary operator, induced by an orientation-preserving
smooth change of coordinates, that maps a normalized state with finite position moments
of every order to a state with infinite expected squared position. -/
theorem change_of_coordinates_finite_to_infinite_expectation :
    ∃ f : ℝ ≃ ℝ, IsOrientationPreservingDiffeo f ∧
    ∃ U : Lp ℂ 2 (volume : Measure ℝ) ≃ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℝ),
      (∀ g : Lp ℂ 2 (volume : Measure ℝ),
        (U g : ℝ → ℂ) =ᵐ[volume] changeOfVariables f (g : ℝ → ℂ)) ∧
    ∃ ψ : Lp ℂ 2 (volume : Measure ℝ), ‖ψ‖ = 1 ∧
      (∀ n : ℕ, Integrable (fun x : ℝ => |x| ^ n * ‖(ψ : ℝ → ℂ) x‖ ^ 2)) ∧
      ¬ Integrable (fun y : ℝ => y ^ 2 * ‖(U ψ : ℝ → ℂ) y‖ ^ 2) := by
  sorry

end UnphysicalHilbert
