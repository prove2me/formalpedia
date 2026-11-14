-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_isolated_variable_literal_score_eq_own_shift
-- name    : StabilityDichotomies.Bijunctive.isolated_variable_literal_score_eq_own_shift
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:31:56.066981+00:00
-- url     : https://prove2.me/theorems/be2161f1-3a3b-4ddc-97a1-2487e3ef3a07
-- title:
--   An isolated literal’s score equals its own shift
-- statement:
--   For a satisfiable original instance, a variable outside all constraint scopes, and arbitrary graph and feasibility thinning masks, each of its literal scores equals its own shift. Thus its output is unaffected by changes to either mask.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean CSPs, STOC 2027, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.9, sensitivity analysis.

import Definitions.Def_StabilityDichotomies_Approximability_Bijunctive
open scoped Classical BigOperators
open StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

theorem StabilityDichotomies.Bijunctive.isolated_variable_literal_score_eq_own_shift {Γ : Language} {V : Type} [Fintype V]
    (rep : TwoCNFRepresentation Γ) (I : Instance Γ V) (hI : Satisfiable I) (v : V)
    (hiso : ∀ c ∈ I.constraints, ∀ k : Fin c.rel.val.arity, c.scope k ≠ v)
    (graphMask feasibleMask : Fin I.constraints.card → Bool) (δ : Literal V → ℝ) (b : Bool) :
    literalScore rep (thinnedInstance I graphMask) (thinnedInstance I feasibleMask) δ (v,b) =
      ((δ (v,b) : ℝ) : WithBot ℝ) := by
  sorry
