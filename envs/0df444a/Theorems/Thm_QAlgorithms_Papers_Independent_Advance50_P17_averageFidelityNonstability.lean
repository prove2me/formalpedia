-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P17_averageFidelityNonstability
-- name    : QAlgorithms.Papers.Independent.Advance50.P17.averageFidelityNonstability
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T11:32:05.303853+00:00
-- url     : https://prove2.me/theorems/026b9113-f855-4ae8-abcd-77946ebf386d
-- title:
--   Section IV B: average fidelity and its A/B/C transforms are not stable
-- statement:
--   Let $F_{\rm ave}$ be the normalized Haar average of squared state fidelity. It obeys $F_{\rm ave}(\mathcal E,\mathcal E)=1$ for every CPTP map, so it fails the diagonal-zero metric axiom. There also exist a positive finite-dimensional CPTP map $\mathcal E$, a unitary ideal $U$, and a positive finite ancilla $A$ for which
--
--   $$g:=F_{\rm ave}(\mathcal I_A\otimes\mathcal E,\mathcal I_A\otimes\mathcal U)\ne f:=F_{\rm ave}(\mathcal E,\mathcal U).$$
--
--   For the same pair, $h(g)\ne h(f)$ for each $h(t)=\arccos\sqrt t$, $\sqrt{2-2\sqrt t}$, and $\sqrt{1-t}$. These transforms are applied after averaging, unlike averaged state metrics.
-- source:
--   Distance measures to compare real and ideal quantum processes, arXiv:quant-ph/0408063v2, PDF p. 7, Section IV B: average fidelity and its A/B/C transforms are not stable

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

/-- Section IV B, PDF p.7: F_ave has diagonal value one, hence is not a metric; it and all
three transforms applied AFTER averaging fail stability, even with unitary ideal process. -/
theorem averageFidelityNonstability :
    (∀ E : FiniteProcess I I, aveFidelity E.val E.val = 1) ∧
    (¬ MetricAxioms (fun E F : FiniteProcess I I => aveFidelity E.val F.val)) ∧
    (∃ d m : ℕ, ∃ hd : 0 < d, ∃ hm : 0 < m,
      letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
      letI : Nonempty (Fin m) := ⟨⟨0,hm⟩⟩
      ∃ E : FiniteProcess (Fin d) (Fin d), ∃ U : Matrix.unitaryGroup (Fin d) ℂ,
        let f := aveFidelity E.val (conjSuperop (U : Matrix (Fin d) (Fin d) ℂ))
        let g := aveFidelity (idTensorSuperop (R := Fin m) E.val)
          (idTensorSuperop (R := Fin m) (conjSuperop (U : Matrix (Fin d) (Fin d) ℂ)))
        g ≠ f ∧ ∀ c : Choice, c ≠ .trace → fidelityTransform c g ≠ fidelityTransform c f) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P17

end
