-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P17_averageNonstability
-- name    : QAlgorithms.Papers.Independent.Advance50.P17.averageNonstability
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T11:30:40.140063+00:00
-- url     : https://prove2.me/theorems/3b0392b3-479f-4eb3-8a5b-fd03d3f7f781
-- title:
--   Section IV B: average distances fail stability
-- statement:
--   For each choice $\Delta\in\{D,A,B,C\}$, there exist positive finite system and ancilla dimensions and CPTP maps $\mathcal E,\mathcal F$ such that
--
--   $$\Delta_{\rm ave}(\mathcal I_A\otimes\mathcal E,\mathcal I_A\otimes\mathcal F)\ne\Delta_{\rm ave}(\mathcal E,\mathcal F).$$
--
--   The average is over the normalized Haar pure-input law on the applicable register. This is an existence claim, without a prescribed dimension or gap constant.
-- source:
--   Distance measures to compare real and ideal quantum processes, arXiv:quant-ph/0408063v2, PDF p. 7, Section IV B: average distances fail stability

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

/-- Section IV B, PDF p.7: for EACH candidate metric there exists a failure of stability;
this makes no assertion about identical pairs or one-dimensional systems. -/
theorem averageNonstability : ∀ c : Choice, ∃ d m : ℕ, ∃ hd : 0 < d, ∃ hm : 0 < m,
    letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
    letI : Nonempty (Fin m) := ⟨⟨0,hm⟩⟩
    ∃ E F : FiniteProcess (Fin d) (Fin d),
      aveDistance (stateDistance c) (idTensorSuperop (R := Fin m) E.val)
        (idTensorSuperop (R := Fin m) F.val) ≠ aveDistance (stateDistance c) E.val F.val := by sorry

end QAlgorithms.Papers.Independent.Advance50.P17

end
