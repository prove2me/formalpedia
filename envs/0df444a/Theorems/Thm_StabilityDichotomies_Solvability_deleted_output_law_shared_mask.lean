-- Prove2me | Theorems.Thm_StabilityDichotomies_Solvability_deleted_output_law_shared_mask
-- name    : StabilityDichotomies.Solvability.deleted_output_law_shared_mask
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T07:23:53.779213+00:00
-- url     : https://prove2.me/theorems/d14c4cb5-1014-4898-a909-dcab6c61c992
-- title:
--   Deleted-instance output law from a forced-absent original mask
-- statement:
--   Let A satisfy the exact thinning output law and let I be satisfiable with c an original constraint occurrence. There exists an original occurrence index such that the output law on I.delete c equals the uniform Bernoulli mixture of the original-instance output with that index forced absent. The result handles duplicate constraints and the independent occurrence orderings selected for the two multisets.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean Constraint Satisfaction Problems, STOC 2027 submission #535, deletion coupling in proof of Theorem 4.3, p. 17, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf

import Definitions.Def_StabilityDichotomies_Approximability_Thinning
noncomputable section
open scoped Classical BigOperators Interval
open MeasureTheory StabilityDichotomies.Solvability

theorem StabilityDichotomies.Solvability.deleted_output_law_shared_mask (Γ : Language) (b : Bool) (ε : ℝ)
    (A : Solver Γ) (hLaw : ThinningOutputLaw Γ b ε A)
    (V : Type) [Fintype V] (I : Instance Γ V) (hSat : Satisfiable I)
    (c : Constraint Γ V) (hc : c ∈ I.constraints) :
    ∃ i : Fin I.constraints.card, ∀ x : V → Bool,
      (A V (I.delete c) x).toReal = ε⁻¹ * ∫ p in (1-ε)..1,
        ∑ mask : Fin I.constraints.card → Bool, retentionWeight p mask *
          (if extremalSolution (thinnedInstance I (Function.update mask i false)) b = x then 1 else 0) := by sorry
