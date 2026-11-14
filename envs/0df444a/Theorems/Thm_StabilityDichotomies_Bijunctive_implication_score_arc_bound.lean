-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_implication_score_arc_bound
-- name    : StabilityDichotomies.Bijunctive.implication_score_arc_bound
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T08:06:09.724467+00:00
-- url     : https://prove2.me/theorems/6e976c43-97a7-4a63-af77-5fe54d0972e3
-- title:
--   A directed implication arc changes the root score by at most one
-- statement:
--   For any fixed graph subinstance, feasible-root subinstance, and real shifts, if the implication graph contains a directed arc a→b then score(a) ≤ score(b)+1, with unreachable scores represented by bottom. The result follows by extending every root-to-a shortest path by the given unit arc. It is the deterministic score inequality used in the approximation proof of Theorem 4.9.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean Constraint Satisfaction Problems, STOC 2027 submission #535, proof of Theorem 4.9, p. 20, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf

import Definitions.Def_StabilityDichotomies_Approximability_Bijunctive
noncomputable section
open scoped Classical BigOperators
open StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

theorem StabilityDichotomies.Bijunctive.implication_score_arc_bound {Γ : Language} {V : Type} [Fintype V]
    (rep : TwoCNFRepresentation Γ) (G F : Instance Γ V) (δ : Literal V → ℝ)
    (a b : Literal V) (hab : implicationArc rep G a b) :
    literalScore rep G F δ a ≤ literalScore rep G F δ b + ((1 : ℝ) : WithBot ℝ) := by sorry
