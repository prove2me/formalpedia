-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P17_stabilizedDiscrimination
-- name    : QAlgorithms.Papers.Independent.Advance50.P17.stabilizedDiscrimination
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T11:35:40.764453+00:00
-- url     : https://prove2.me/theorems/e06c18c2-cdfd-4f33-9a7e-ec9048107427
-- title:
--   Section IV C: stabilized trace distance as optimal discrimination bias
-- statement:
--   Let $\mathcal E,\mathcal F$ be CPTP maps on a register of dimension $d\ge1$. For any positive finite ancilla $S$, unit pure input on $S\otimes I$, and joint binary POVM effect $M$, the equal-prior success probability of distinguishing the two channel outputs is bounded by
--
--   $$P_{\rm succ}\le\frac{1+D_{\rm stab}(\mathcal E,\mathcal F)}2.$$
--
--   An ancilla of dimension $d$, a normalized pure input, and a joint binary POVM attain equality. Thus the bias above one half is $D_{\rm stab}/2$.
-- source:
--   Distance measures to compare real and ideal quantum processes, arXiv:quant-ph/0408063v2, PDF p. 8, Section IV C: stabilized trace distance as optimal discrimination bias

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

/-- Section IV C, PDF p.8: arbitrary-ancilla discrimination success is (1+D_stab)/2;
an input-sized ancilla and a joint binary POVM attain it. Bias means success minus 1/2. -/
theorem stabilizedDiscrimination (E F : FiniteProcess I I) :
    (∀ (S : Type) [Fintype S] [DecidableEq S] [Nonempty S], ∀ psi : ProcessPureInput (S × I),
      ∀ M : Matrix (S × I) (S × I) ℂ, IsEffect M →
        binarySuccess (idTensorSuperop E.val (pureDensity psi.val))
          (idTensorSuperop F.val (pureDensity psi.val)) M ≤
            (1 + stabDistance (stateDistance .trace) E.val F.val) / 2) ∧
    (∃ psi : ProcessPureInput (I × I), ∃ M : Matrix (I × I) (I × I) ℂ, IsEffect M ∧
      binarySuccess (idTensorSuperop E.val (pureDensity psi.val))
        (idTensorSuperop F.val (pureDensity psi.val)) M =
          (1 + stabDistance (stateDistance .trace) E.val F.val) / 2) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P17

end
