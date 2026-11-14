-- Prove2me | Theorems.Thm_StabilityDichotomies_Solvability_deleted_output_law_at_original_index
-- name    : StabilityDichotomies.Solvability.deleted_output_law_at_original_index
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T07:28:10.749561+00:00
-- url     : https://prove2.me/theorems/36d6c0ba-dec4-401c-83a8-15c3cef1a4aa
-- title:
--   Deleted-instance thinning law at each original occurrence index
-- statement:
--   Let A have the exact thinning law on satisfiable inputs. For every original occurrence index i, the output law on the instance obtained by erasing that occurrence’s constraint value equals the uniform Bernoulli mixture of the original-instance output with coordinate i forced absent. The equality retains multiplicities and aligns the two independent multiset enumerations.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean Constraint Satisfaction Problems, STOC 2027 submission #535, deletion coupling in proof of Theorem 4.3, p. 17, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf

import Definitions.Def_StabilityDichotomies_Approximability_Thinning
noncomputable section
open scoped Classical BigOperators Interval
open MeasureTheory StabilityDichotomies.Solvability

theorem StabilityDichotomies.Solvability.deleted_output_law_at_original_index (Γ : Language) (b : Bool) (ε : ℝ)
    (A : Solver Γ) (hLaw : ThinningOutputLaw Γ b ε A)
    (V : Type) [Fintype V] (I : Instance Γ V) (hSat : Satisfiable I)
    (i : Fin I.constraints.card) (x : V → Bool) :
      (A V (I.delete (occurrenceAt I i)) x).toReal = ε⁻¹ * ∫ p in (1-ε)..1,
        ∑ mask : Fin I.constraints.card → Bool, retentionWeight p mask *
          (if extremalSolution (thinnedInstance I (Function.update mask i false)) b = x then 1 else 0) := by sorry
