-- Prove2me | Theorems.Thm_PrivateAgnosticHalfspace_Gaussian_lemma_B_7
-- name    : PrivateAgnosticHalfspace.Gaussian.lemma_B_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T11:24:42.640212+00:00
-- url     : https://prove2.me/theorems/83a92a69-bc94-4c2a-b5fd-020c918986de
-- title:
--   Lemma B.7 — expected uniform absolute-loss deviation
-- statement:
--   Let $P$ be a probability law on $X\times\{-1,1\}$ and let $\phi:X\to\mathbb R^D$ be measurable with finite second moment $\mathbb E\|\phi(X)\|_2^2\le D$. For an i.i.d. sample $S$ of size $n\ge1$, define population and empirical absolute losses $L_P$ and $\widehat L_S$. For every radius $R>0$,
--   $$
--   \mathbb E_{S\sim P^n}\sup_{\|v\|_2\le R}
--   \bigl(L_P(v)-\widehat L_S(v)\bigr)\le2R\sqrt{D/n}.
--   $$
--   The statement also records integrability of each population loss and of this supremum, and boundedness above of each sample's optimization set. The supremum is one-sided; the feature map need not be bounded.
--
--   This controls statistical error of regression using only a second-moment feature bound and the standing binary-label model.
--
--   Differences from the source:
--   - encoding: a finite second-moment expectation and an empirical mean → Integrable of the squared feature norm and positive n; reason: gives the source expectation its finite meaning and excludes division by zero, without imposing bounded features
--   - encoding: the expected one-sided supremum over the Euclidean ball → sSup of its image with boundedness and integrability conclusions; reason: prevents total real extrema or Bochner integrals from silently taking default values
-- source:
--   Giorgio Racca, Amartya Sanyal, Vikrant Singhal, STOC 2027 submission #1006 (October 2026), p. 22, Lemma B.7; canonical PDF sha256 f0122a33e29daa624b530bdd0b071998d8e44197b30449b0cb3213289645cec7

import Definitions.Def_PrivateAgnosticHalfspace_Gaussian_Regression

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
set_option autoImplicit false

namespace PrivateAgnosticHalfspace.Gaussian

theorem lemma_B_7 {X : Type*} [MeasurableSpace X]
    (D n : ℕ) (hn : 0 < n) (P : Measure (X × Bool)) [IsProbabilityMeasure P]
    (φ : X → Vec D) (hφ : Measurable φ)
    (hfinite : Integrable (fun z : X × Bool => ‖φ z.1‖ ^ 2) P)
    (hmoment : (∫ z, ‖φ z.1‖ ^ 2 ∂P) ≤ D) (R : ℝ) (hR : 0 < R) :
    (∀ v, Integrable (fun z : X × Bool => |inner ℝ v (φ z.1) - label z.2|) P) ∧
    (∀ S : Fin n → X × Bool,
      BddAbove ((fun v => risk D φ P v - empiricalRisk D φ S v) '' Metric.closedBall 0 R)) ∧
    Integrable (deviation D φ P R (n := n)) (Measure.pi (fun _ : Fin n => P)) ∧
    (∫ S, deviation D φ P R S ∂Measure.pi (fun _ : Fin n => P)) ≤
      2 * R * Real.sqrt ((D : ℝ) / n) := by sorry

end PrivateAgnosticHalfspace.Gaussian
