-- Prove2me | Theorems.Thm_StabilityDichotomies_Solvability_integrated_occurrence_violation
-- name    : StabilityDichotomies.Solvability.integrated_occurrence_violation
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T06:49:27.601413+00:00
-- url     : https://prove2.me/theorems/472328cb-395d-4963-9eed-0846a2b02f41
-- title:
--   Per-occurrence violation bound for the thinning output law
-- statement:
--   Let I be a satisfiable Horn or dual-Horn instance and 0 < ε ≤ 1. Under the exact thinning experiment of Definition 4.2, any fixed constraint occurrence is violated by the extremal output with probability at most ε/2. The formula represents the uniform mixture of the independent Bernoulli-p mask weights and applies separately to each occurrence, including duplicates. This establishes the individual error bound in the approximation part of Theorem 4.3.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean Constraint Satisfaction Problems, STOC 2027 submission #535, Definition 4.2 and proof of Theorem 4.3, p. 16, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf

import Definitions.Def_StabilityDichotomies_Approximability_Thinning
noncomputable section
open scoped Classical BigOperators Interval
open MeasureTheory StabilityDichotomies.Solvability

theorem StabilityDichotomies.Solvability.integrated_occurrence_violation (Γ : Language) (b : Bool)
    (hΓ : ∀ R ∈ Γ.relations, ∀ x y : Fin R.arity → Bool,
      x ∈ R.tuples → y ∈ R.tuples →
      (fun i => if b then x i || y i else x i && y i) ∈ R.tuples)
    (V : Type) [Fintype V] (I : Instance Γ V) (hSat : Satisfiable I)
    (i : Fin I.constraints.card) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ε⁻¹ * ∫ p in (1 - ε)..1,
      ∑ mask : Fin I.constraints.card → Bool, retentionWeight p mask *
      (if (occurrenceAt I i).Satisfied (extremalSolution (thinnedInstance I mask) b) then 0 else 1) ≤ ε / 2 := by sorry
