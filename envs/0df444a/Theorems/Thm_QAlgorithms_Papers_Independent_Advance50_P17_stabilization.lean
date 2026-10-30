-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P17_stabilization
-- name    : QAlgorithms.Papers.Independent.Advance50.P17.stabilization
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T11:34:25.240544+00:00
-- url     : https://prove2.me/theorems/70f5c8d1-5bdf-4055-a0de-ed7e56bc41db
-- title:
--   Section IV C, Eq.(18), Appendix A1: stabilization by an input-sized ancilla
-- statement:
--   Let $\mathcal E,\mathcal F$ be CPTP maps on a system of dimension $d\ge1$. For each $\Delta\in\{D,A,B,C\}$ and every finite ancilla $S$ with $\dim S\ge d$,
--
--   $$\Delta_{\max}(\mathcal I_S\otimes\mathcal E,\mathcal I_S\otimes\mathcal F)=\Delta_{\rm stab}(\mathcal E,\mathcal F).$$
--
--   The analogous minimum squared fidelity equals $F_{\rm stab}$. Consequently both stabilized quantities remain unchanged after adjoining any positive finite identity register to the original system. The cutoff is the input dimension, and tensor-factor orders are canonical.
-- source:
--   Distance measures to compare real and ideal quantum processes, arXiv:quant-ph/0408063v2, PDF p. 12, Section IV C, Eq.(18), Appendix A1: stabilization by an input-sized ancilla

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

/-- Section IV C, PDF p.8, Eq.(18), Appendix A1, p.12: all ancillas of dimension at least d
achieve the same concrete maximum/minimum. Stabilized measures are stable on extension. -/
theorem stabilization (E F : FiniteProcess I I) :
    (∀ (S : Type) [Fintype S] [DecidableEq S] [Nonempty S], Fintype.card I ≤ Fintype.card S →
      (∀ c : Choice, maxDistance (stateDistance c) (idTensorSuperop (R := S) E.val)
        (idTensorSuperop (R := S) F.val) = stabDistance (stateDistance c) E.val F.val) ∧
      minFidelity (idTensorSuperop (R := S) E.val) (idTensorSuperop (R := S) F.val) =
        stabFidelity E.val F.val) ∧
    (∀ c : Choice, stabDistance (stateDistance c) (idTensorSuperop (R := J) E.val)
      (idTensorSuperop (R := J) F.val) = stabDistance (stateDistance c) E.val F.val) ∧
    stabFidelity (idTensorSuperop (R := J) E.val) (idTensorSuperop (R := J) F.val) =
      stabFidelity E.val F.val := by sorry

end QAlgorithms.Papers.Independent.Advance50.P17

end
