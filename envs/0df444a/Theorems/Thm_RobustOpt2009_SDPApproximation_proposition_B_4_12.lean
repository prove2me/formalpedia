-- Prove2me | Theorems.Thm_RobustOpt2009_SDPApproximation_proposition_B_4_12
-- name    : RobustOpt2009.SDPApproximation.proposition_B_4_12
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-22T03:43:08.33976+00:00
-- url     : https://prove2.me/theorems/48ef2b9a-c2ae-487d-8de4-14d3e7937c52
-- title:
--   Proposition B.4.12 — Gaussian products of Euclidean norms
-- statement:
--   Let $p,q,n$ be positive integers.
--
--   1. For $L\in\mathbb C^{p\times n}$, $R\in\mathbb C^{q\times n}$ and a standard complex Gaussian vector $\chi$ with complex covariance $I_n$,
--   $$\mathbb E[\|L\chi\|_2\|R\chi\|_2]\ge\frac\pi4\|L\|_F\|R\|_F.$$
--   2. For $L\in\mathbb R^{p\times n}$, $R\in\mathbb R^{q\times n}$ and a standard real Gaussian vector $\xi$,
--   $$\mathbb E[\|L\xi\|_2\|R\xi\|_2]\ge\frac2\pi\|L\|_F\|R\|_F.$$
--   Both products are integrable, including when either matrix is zero. These estimates are quantitative ingredients of the appendix's matrix cube analysis.
--
--   **Formalization Note** The book writes $\|L\|_2$ for the Frobenius matrix norm; it is written $\|L\|_F$ here to distinguish it from an operator norm. Integrability is a conclusion expressing that the displayed expectations exist, never an added hypothesis. The complex law uses independent real and imaginary parts with variance $1/2$.
-- source:
--   Ben-Tal, El Ghaoui and Nemirovski, Robust Optimization, Princeton University Press, 2009, https://doi.org/10.1515/9781400831050, Proposition B.4.12, printed p. 502 (PDF p. 528), equations (B.4.35)–(B.4.36)

import Mathlib

open Matrix MeasureTheory ProbabilityTheory

namespace RobustOpt2009.SDPApproximation

/-- Proposition B.4.12: both expectations, including their integrability,
with all Gaussian laws and norm formulas expanded in the statement. -/
theorem proposition_B_4_12 :
    (∀ (p q n : ℕ), 0 < p → 0 < q → 0 < n →
      ∀ (L : Matrix (Fin p) (Fin n) ℂ) (R : Matrix (Fin q) (Fin n) ℂ),
        let γ : Measure (Fin n → ℝ × ℝ) :=
          Measure.pi fun _ => (gaussianReal 0 (1 / 2)).prod (gaussianReal 0 (1 / 2))
        let g : (Fin n → ℝ × ℝ) → ℝ := fun x =>
          let z : Fin n → ℂ := fun i => ⟨(x i).1, (x i).2⟩
          Real.sqrt (∑ i, ‖(L *ᵥ z) i‖ ^ 2) * Real.sqrt (∑ i, ‖(R *ᵥ z) i‖ ^ 2)
        Integrable g γ ∧ (∫ x, g x ∂γ) ≥ (Real.pi / 4) *
          Real.sqrt (∑ i, ∑ j, ‖L i j‖ ^ 2) * Real.sqrt (∑ i, ∑ j, ‖R i j‖ ^ 2)) ∧
    (∀ (p q n : ℕ), 0 < p → 0 < q → 0 < n →
      ∀ (L : Matrix (Fin p) (Fin n) ℝ) (R : Matrix (Fin q) (Fin n) ℝ),
        let γ : Measure (Fin n → ℝ) := Measure.pi fun _ => gaussianReal 0 1
        let g : (Fin n → ℝ) → ℝ := fun x =>
          Real.sqrt (∑ i, ((L *ᵥ x) i) ^ 2) * Real.sqrt (∑ i, ((R *ᵥ x) i) ^ 2)
        Integrable g γ ∧ (∫ x, g x ∂γ) ≥ (2 / Real.pi) *
          Real.sqrt (∑ i, ∑ j, (L i j) ^ 2) * Real.sqrt (∑ i, ∑ j, (R i j) ^ 2)) := by sorry

end RobustOpt2009.SDPApproximation
