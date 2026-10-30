-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P17_minimumFidelityNonstability
-- name    : QAlgorithms.Papers.Independent.Advance50.P17.minimumFidelityNonstability
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T11:33:43.934779+00:00
-- url     : https://prove2.me/theorems/ff5c81d8-42a6-4b4e-a367-20517da0483e
-- title:
--   Section IV C: fidelity-based unstabilized worst-case measures fail stability
-- statement:
--   There exist positive finite system and ancilla dimensions and CPTP maps $\mathcal E,\mathcal F$ such that their pure-input minimum squared fidelity satisfies
--
--   $$F_{\min}(\mathcal I_A\otimes\mathcal E,\mathcal I_A\otimes\mathcal F)\ne F_{\min}(\mathcal E,\mathcal F).$$
--
--   For that same pair each pure-input maximum based on $A,B,C$ also changes on identity extension. Thus the fidelity-derived unstabilized worst-case measures fail stability.
-- source:
--   Distance measures to compare real and ideal quantum processes, arXiv:quant-ph/0408063v2, PDF p. 8, Section IV C: fidelity-based unstabilized worst-case measures fail stability

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P17

noncomputable section

open MeasureTheory Filter

open scoped Matrix ComplexConjugate Topology

namespace QAlgorithms.Papers.Independent.Advance50.P17

open QAlgorithms.Papers.Independent.Information100.P53 (fidelity)

open QAlgorithms.Papers.Independent.Information100.P08 (canonicalPurification)

open QAlgorithms.Papers.Independent.Information100.P75 (hermitianReal)

variable {I J K : Type} [Fintype I] [Fintype J] [Fintype K]
  [DecidableEq I] [DecidableEq J] [DecidableEq K]
  [Nonempty I] [Nonempty J] [Nonempty K]

/-- Section IV C, PDF p.8: F_min and the A,B,C worst-case transforms fail stability. -/
theorem minimumFidelityNonstability : ∃ d m : ℕ, ∃ hd : 0 < d, ∃ hm : 0 < m,
    letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
    letI : Nonempty (Fin m) := ⟨⟨0,hm⟩⟩
    ∃ E F : FiniteProcess (Fin d) (Fin d),
      minFidelity (idTensorSuperop (R := Fin m) E.val) (idTensorSuperop (R := Fin m) F.val) ≠
        minFidelity E.val F.val ∧
      ∀ c : Choice, c ≠ .trace →
        maxDistance (stateDistance c) (idTensorSuperop (R := Fin m) E.val)
          (idTensorSuperop (R := Fin m) F.val) ≠ maxDistance (stateDistance c) E.val F.val := by sorry

end QAlgorithms.Papers.Independent.Advance50.P17

end
