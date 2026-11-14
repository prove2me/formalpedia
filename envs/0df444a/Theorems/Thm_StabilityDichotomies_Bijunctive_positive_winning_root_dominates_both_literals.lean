-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_positive_winning_root_dominates_both_literals
-- name    : StabilityDichotomies.Bijunctive.positive_winning_root_dominates_both_literals
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:58:11.645269+00:00
-- url     : https://prove2.me/theorems/f5dde13d-87ae-4eb0-aa51-8a82ca3b63fe
-- title:
--   A positive winning root maximizes over both literal targets
-- statement:
--   For nested graph and satisfiable feasibility instances with positive shifts, each variable has a feasible winning root whose positive shifted-distance score dominates every feasible contribution reaching either literal. This root cannot reach the opposite literal. The winning literal agrees exactly with the algorithm output.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean CSPs, STOC 2027, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.9, feasibility-root sensitivity step.

import Definitions.Def_StabilityDichotomies_Approximability_Bijunctive
open scoped Classical BigOperators
open StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

theorem StabilityDichotomies.Bijunctive.positive_winning_root_dominates_both_literals {Γ : Language} {V : Type} [Fintype V]
    (rep : TwoCNFRepresentation Γ) (G F : Instance Γ V) (hF : Satisfiable F)
    (hsub : ∀ c ∈ G.constraints, c ∈ F.constraints)
    (δ : Literal V → ℝ) (hδ : ∀ a, 0 < δ a) (v : V) :
    ∃ (root : Literal V) (n : ℕ) (w : Bool),
      w = decide (literalScore rep G F δ (v,false) < literalScore rep G F δ (v,true)) ∧
      feasibleLiteral F root ∧ implicationDistance rep G root (v,w) = some n ∧
      literalScore rep G F δ (v,w) = ((δ root - n : ℝ) : WithBot ℝ) ∧
      0 < δ root - n ∧
      (∀ (r : Literal V) (m : ℕ) (z : Bool), feasibleLiteral F r →
        implicationDistance rep G r (v,z) = some m → δ r - m ≤ δ root - n) ∧
      ¬ ∃ m, WalkLength (implicationArc rep G) m root (v,!w) := by
  sorry
