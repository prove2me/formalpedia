-- Prove2me | Theorems.Thm_StabilityDichotomies_Solvability_occurrence_violation_le_omission
-- name    : StabilityDichotomies.Solvability.occurrence_violation_le_omission
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T06:46:35.186198+00:00
-- url     : https://prove2.me/theorems/027cb932-e7dc-4b51-941d-aed5e3ae956f
-- title:
--   Thinning violation is bounded by omission at fixed retention probability
-- statement:
--   Let I be a satisfiable Horn or dual-Horn instance. Fix an occurrence c and a retention probability p in [0,1]. Under independent Bernoulli-p retention, the probability that the extremal output violates c is at most the probability that c was omitted. This holds occurrence by occurrence, including repeated constraints, and is the pointwise approximation step in the proof of Theorem 4.3.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean Constraint Satisfaction Problems, STOC 2027 submission #535, proof of Theorem 4.3, p. 16, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf

import Definitions.Def_StabilityDichotomies_Approximability_Thinning
noncomputable section
open scoped Classical BigOperators
open StabilityDichotomies.Solvability

theorem StabilityDichotomies.Solvability.occurrence_violation_le_omission (Γ : Language) (b : Bool)
    (hΓ : ∀ R ∈ Γ.relations, ∀ x y : Fin R.arity → Bool,
      x ∈ R.tuples → y ∈ R.tuples →
      (fun i => if b then x i || y i else x i && y i) ∈ R.tuples)
    (V : Type) [Fintype V] (I : Instance Γ V) (hSat : Satisfiable I)
    (i : Fin I.constraints.card) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (∑ mask : Fin I.constraints.card → Bool, retentionWeight p mask *
      (if (occurrenceAt I i).Satisfied (extremalSolution (thinnedInstance I mask) b) then 0 else 1)) ≤
    (∑ mask : Fin I.constraints.card → Bool, retentionWeight p mask * (if mask i then 0 else 1)) := by sorry
