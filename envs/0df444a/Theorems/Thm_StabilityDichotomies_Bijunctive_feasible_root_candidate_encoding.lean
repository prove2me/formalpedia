-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_feasible_root_candidate_encoding
-- name    : StabilityDichotomies.Bijunctive.feasible_root_candidate_encoding
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:59:45.800673+00:00
-- url     : https://prove2.me/theorems/c82b1aa2-f3a6-45a2-bc5f-d65c31a8c69b
-- title:
--   Encode feasible roots by fixed labels and nonnegative distances
-- statement:
--   Fix a graph subinstance contained in a base feasibility instance and a variable. There is a finite set of candidate roots, a fixed Boolean label for each root, and nonnegative root distances, all independent of shifts and later constraints. For every satisfiable feasibility extension and positive shifts, some feasible candidate has positive shifted score, maximizes over all currently feasible candidates, and has label equal to the algorithm output.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean CSPs, STOC 2027, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.9, feasibility-root sensitivity step.

import Definitions.Def_StabilityDichotomies_Approximability_Bijunctive
open scoped Classical BigOperators
open StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

theorem StabilityDichotomies.Bijunctive.feasible_root_candidate_encoding {Γ : Language} {V : Type} [Fintype V]
    (rep : TwoCNFRepresentation Γ) (G F₀ : Instance Γ V) (v : V)
    (hG : ∀ c ∈ G.constraints, c ∈ F₀.constraints) :
    ∃ (C : Finset (Literal V)) (label : Literal V → Bool) (d : Literal V → ℝ),
      (∀ r ∈ C, 0 ≤ d r) ∧
      ∀ (F : Instance Γ V), (∀ c ∈ F₀.constraints, c ∈ F.constraints) → Satisfiable F →
      ∀ δ : Literal V → ℝ, (∀ r, 0 < δ r) →
        ∃ r ∈ C, feasibleLiteral F r ∧
          label r = decide (literalScore rep G F δ (v,false) < literalScore rep G F δ (v,true)) ∧
          0 < δ r - d r ∧
          ∀ q ∈ C, feasibleLiteral F q → δ q - d q ≤ δ r - d r := by
  sorry
