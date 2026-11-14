-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_bijunctive_output_event_measurable
-- name    : StabilityDichotomies.Bijunctive.bijunctive_output_event_measurable
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T07:59:30.978178+00:00
-- url     : https://prove2.me/theorems/dd1470b0-63b9-449d-84cf-33d34794587f
-- title:
--   Measurability of the bijunctive algorithm output events
-- statement:
--   For a fixed represented CSP instance, error parameter ε, and Boolean assignment x, the set of priority, cutoff, and shift vectors for which the Definition 4.8 deterministic map outputs x is measurable. This establishes that the source algorithm can be pushed forward from its continuous product seed measure.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean Constraint Satisfaction Problems, STOC 2027 submission #535, Definition 4.8, p. 19, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf

import Definitions.Def_StabilityDichotomies_Approximability_BijunctiveLaw
noncomputable section
open scoped Classical
open MeasureTheory StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

theorem StabilityDichotomies.Bijunctive.bijunctive_output_event_measurable {Γ : Language} {V : Type} [Fintype V]
    (rep : TwoCNFRepresentation Γ) (I : Instance Γ V) (ε : ℝ) (x : V → Bool) :
    MeasurableSet {s : (Fin I.constraints.card → ℝ) × ℝ × (Literal V → ℝ) |
      bijunctiveOutput rep I ε s.1 s.2.1 s.2.2 = x} := by sorry
