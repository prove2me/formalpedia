-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_satisfiable_positive_shift_has_positive_literal_score
-- name    : StabilityDichotomies.Bijunctive.satisfiable_positive_shift_has_positive_literal_score
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T08:07:03.165661+00:00
-- url     : https://prove2.me/theorems/e77a1e28-3b92-4058-ae68-aec6424ebced
-- title:
--   A satisfiable instance gives each variable a positive literal score
-- statement:
--   If the feasible-root instance is satisfiable and every literal shift is positive, then for every variable at least one of its positive and negative literals has strictly positive score, regardless of the graph subinstance. The satisfying assignment provides a feasible literal whose zero-length self path contributes its own positive shift. This is the deterministic positivity observation in the source proof of Theorem 4.9.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean Constraint Satisfaction Problems, STOC 2027 submission #535, proof of Theorem 4.9, p. 19, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf

import Definitions.Def_StabilityDichotomies_Approximability_Bijunctive
noncomputable section
open scoped Classical BigOperators
open StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

theorem StabilityDichotomies.Bijunctive.satisfiable_positive_shift_has_positive_literal_score {Γ : Language} {V : Type} [Fintype V]
    (rep : TwoCNFRepresentation Γ) (G F : Instance Γ V) (hF : Satisfiable F)
    (δ : Literal V → ℝ) (hδ : ∀ a, 0 < δ a) (v : V) :
    ∃ b : Bool, (0 : WithBot ℝ) < literalScore rep G F δ (v,b) := by sorry
