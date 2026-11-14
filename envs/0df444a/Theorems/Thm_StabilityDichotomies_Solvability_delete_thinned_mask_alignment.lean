-- Prove2me | Theorems.Thm_StabilityDichotomies_Solvability_delete_thinned_mask_alignment
-- name    : StabilityDichotomies.Solvability.delete_thinned_mask_alignment
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T07:23:52.706434+00:00
-- url     : https://prove2.me/theorems/93c4e167-83b4-4d88-a0df-8791ab26063f
-- title:
--   Forced-absent thinning equals erased-instance thinning
-- statement:
--   Given a value-preserving equivalence between original occurrence indices and an optional index of the instance with one copy of c erased, force the distinguished original coordinate absent and transport every remaining mask bit through the equivalence. The two thinned constraint multisets are exactly equal, including multiplicities. This is the deterministic alignment step for the deletion coupling.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean Constraint Satisfaction Problems, STOC 2027 submission #535, deletion coupling in proof of Theorem 4.3, p. 17, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf

import Definitions.Def_StabilityDichotomies_Approximability_Thinning
noncomputable section
open scoped Classical BigOperators Interval
open MeasureTheory StabilityDichotomies.Solvability

theorem StabilityDichotomies.Solvability.delete_thinned_mask_alignment {Γ : Language} {V : Type} (I : Instance Γ V)
    (c : Constraint Γ V) (hc : c ∈ I.constraints)
    (e : Fin I.constraints.card ≃ Option (Fin (I.delete c).constraints.card))
    (he : ∀ j, (e j).elim c (occurrenceAt (I.delete c)) = occurrenceAt I j)
    (mask : Fin I.constraints.card → Bool) :
    thinnedInstance I (Function.update mask (e.symm none) false) =
      thinnedInstance (I.delete c) (fun k => mask (e.symm (some k))) := by sorry
