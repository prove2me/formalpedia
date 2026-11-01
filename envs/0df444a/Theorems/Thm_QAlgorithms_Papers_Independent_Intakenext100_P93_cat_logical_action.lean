-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P93_cat_logical_action
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P93.cat_logical_action
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:34:11.392973+00:00
-- url     : https://prove2.me/theorems/34f3b17d-84a6-4a29-b108-0ab3036d5234
-- title:
--   Cat Codes for Pauli Channels: syndrome and unrecovered logical action
-- statement:
--   Let $m=k+1\ge1$ and encode a normalized logical qubit $|\psi\rangle$ by $|b\rangle\mapsto|b\rangle^{\otimes m}$. For physical bit strings $u,v\in\{0,1\}^m$, use the ordered Pauli $X^uZ^v$. Apply the coherent cat decoder that retains the first qubit and the $Z_1Z_j$ syndrome, without a recovery operation. Its exact output is
--
--   $$
--   \operatorname{Dec}\,X^uZ^v\operatorname{Enc}|\psi\rangle
--   =X^{u_1}Z^{\bigoplus_{j=1}^m v_j}|\psi\rangle\otimes
--   |u_1\oplus u_2,\ldots,u_1\oplus u_m\rangle.
--   $$
--
--   The formula fixes both the syndrome and the unrecovered logical label. The empty syndrome at $m=1$ is included; source wire 1 is index 0 in the formalization.
-- source:
--   Degenerate Quantum Codes for Pauli Channels, arXiv:quant-ph/0604107v2, PDF p. 2, Cat Codes for Pauli Channels: syndrome and unrecovered logical action

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P93

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P93

open QAlgorithms

open scoped BigOperators ComplexConjugate Matrix

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Smith--Smolin, PDF p.2, Cat Codes for Pauli Channels: exact unrecovered
ordered-Pauli action and deterministic stabilizer syndrome. m=k+1 is positive;
wire 1 in the source is Fin index 0. -/
theorem cat_logical_action (k : ℕ) (u v : Qubits (k + 1))
    (psi : EuclideanSpace ℂ Bool) (hpsi : ‖psi‖ = 1) :
    QAlgorithms.Papers.Independent.Advance50.P15.repetitionDecode (QAlgorithms.Papers.Independent.Advance50.P15.physicalPauli u v (QAlgorithms.Papers.Independent.Advance50.P15.repetitionEncode k psi)) =
      WithLp.toLp 2 (fun z : Bool × Qubits k =>
        QAlgorithms.Papers.Independent.Advance50.P15.logicalPauli (u 0) (dotBits v (fun _ => true)) psi z.1 *
          (ket (QAlgorithms.Papers.Independent.Advance50.P15.repetitionSyndrome u)) z.2) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P93

end
