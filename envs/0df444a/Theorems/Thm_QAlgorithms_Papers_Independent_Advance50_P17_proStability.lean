-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P17_proStability
-- name    : QAlgorithms.Papers.Independent.Advance50.P17.proStability
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T11:25:16.766231+00:00
-- url     : https://prove2.me/theorems/5efa4ac8-d59e-4d32-bb7d-93ff125671a3
-- title:
--   Section IV A: stability of process-matrix distances
-- statement:
--   Let a finite-register state-distance family $\Delta$ be invariant under canonical basis reindexing and adjoining the same normalized tensor factor. For any fixed CPTP maps $\mathcal E,\mathcal F$ and any positive finite ancilla $A$, the normalized reference-first Choi construction satisfies
--
--   $$\Delta_{\rm pro}(\mathcal I_A\otimes\mathcal E,\mathcal I_A\otimes\mathcal F)=\Delta_{\rm pro}(\mathcal E,\mathcal F).$$
--
--   This identity holds in particular for $D,A,B,C$, and squared process fidelity $F_{\rm pro}$ is also stable. Tensor-factor orders are identified by their canonical permutation.
-- source:
--   Distance measures to compare real and ideal quantum processes, arXiv:quant-ph/0408063v2, PDF p. 5, Section IV A: stability of process-matrix distances

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

/-- Section IV A, PDF p.5: process distances inherit state tensor stability after the canonical
reference-first tensor permutation; this includes the four metrics and squared F_pro itself. -/
theorem proStability (delta : FiniteStateDistance) (hs : StateStable delta) (E F : FiniteProcess I I) :
    proDistance delta (idTensorSuperop (R := J) E.val) (idTensorSuperop (R := J) F.val) =
      proDistance delta E.val F.val ∧
    (∀ c : Choice, proDistance (stateDistance c) (idTensorSuperop (R := J) E.val)
      (idTensorSuperop (R := J) F.val) = proDistance (stateDistance c) E.val F.val) ∧
    proFidelity (idTensorSuperop (R := J) E.val) (idTensorSuperop (R := J) F.val) =
      proFidelity E.val F.val := by sorry

end QAlgorithms.Papers.Independent.Advance50.P17

end
