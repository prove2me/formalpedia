-- Prove2me | Theorems.Thm_RhinViola_integerLinearFormExponentialCriterion
-- name    : RhinViola.integerLinearFormExponentialCriterion
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-05T22:14:29.356673+00:00
-- url     : https://prove2.me/theorems/eeb8ac57-e0c5-43b7-a9c2-53a66cf3486e
-- title:
--   Rhin–Viola integer linear-form criterion from eventual exponential estimates
-- statement:
--   Suppose integer linear forms f_n=a_n-b_n α are eventually nonzero and, for every sufficiently small positive slack δ, satisfy exp(-(σ+δ)n)≤|f_n|≤exp(-(σ-δ)n) and |b_n|≤exp((ρ+δ)n), with σ>0 and ρ≥0. Then for every ε>0, all sufficiently large positive denominators q and every integer numerator p satisfy q^(-(1+ρ/σ+ε))<|α-p/q|. This is the source-faithful quantitative content of Rhin and Viola's Lemma 4, expressed through eventual exponential estimates.
-- source:
--   G. Rhin and C. Viola, On the irrationality measure of ζ(2), Annales de l'Institut Fourier 43 (1993), pp. 91–92, Lemma 4.

import Theorems.Thm_RhinViola_existsExponentSlack
import Theorems.Thm_RhinViola_ceilLogIndexBounds
import Theorems.Thm_RhinViola_ceilLogIndexEventuallyGe
import Theorems.Thm_RhinViola_coefficientNonzeroOfSmallLinearForm
import Theorems.Thm_RhinViola_selectedIndexErrorLowerBound
import Theorems.Thm_RhinViola_ceilIndexPowerLowerBound
import Theorems.Thm_RhinViola_eventuallyAbsorbPositiveConstant
import Mathlib.Tactic

theorem RhinViola.integerLinearFormExponentialCriterion
    (α σ ρ ε : ℝ) (a b : ℕ → ℤ)
    (hσ : 0 < σ) (hρ : 0 ≤ ρ) (hε : 0 < ε)
    (hbounds : ∀ δ : ℝ, 0 < δ → δ < σ →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        let f : ℝ := (a n : ℝ) - (b n : ℝ) * α
        f ≠ 0 ∧
        Real.exp (-((σ + δ) * (n : ℝ))) ≤ |f| ∧
        |f| ≤ Real.exp (-((σ - δ) * (n : ℝ))) ∧
        |(b n : ℝ)| ≤ Real.exp ((ρ + δ) * (n : ℝ))) :
    ∃ Q : ℕ, ∀ p : ℤ, ∀ q : ℕ, Q ≤ q → 0 < q →
      (q : ℝ) ^ (-(1 + ρ / σ + ε)) <
        |α - (p : ℝ) / (q : ℝ)| := by sorry
