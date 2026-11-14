-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_isolated_subinstance_literal_score_eq_own_shift
-- name    : StabilityDichotomies.Bijunctive.isolated_subinstance_literal_score_eq_own_shift
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:08:28.75517+00:00
-- url     : https://prove2.me/theorems/15cd032b-6d53-451d-8f65-3bd432981424
-- title:
--   An isolated literal’s score is independent of subinstances
-- statement:
--   For a satisfiable original instance and a variable outside every constraint scope, each literal’s score is its own shift for any graph and feasibility subinstances contained in the original instance. Thus isolated variables have no graph-step or feasibility-step changes.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean CSPs, STOC 2027, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.9, sensitivity analysis.

import Definitions.Def_StabilityDichotomies_Approximability_Bijunctive
open scoped Classical BigOperators
open StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

theorem StabilityDichotomies.Bijunctive.isolated_subinstance_literal_score_eq_own_shift {Γ : Language} {V : Type} [Fintype V]
    (rep : TwoCNFRepresentation Γ) (I : Instance Γ V) (hI : Satisfiable I) (v : V)
    (hiso : ∀ c ∈ I.constraints, ∀ k : Fin c.rel.val.arity, c.scope k ≠ v)
    (G F : Instance Γ V) (hG : ∀ c ∈ G.constraints, c ∈ I.constraints)
    (hF : ∀ c ∈ F.constraints, c ∈ I.constraints) (δ : Literal V → ℝ) (b : Bool) :
    literalScore rep G F δ (v,b) =
      ((δ (v,b) : ℝ) : WithBot ℝ) := by
  sorry
