-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P46_ocb_notPurifiable
-- name    : QAlgorithms.Papers.Independent.Intake100.P46.ocb_notPurifiable
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:07:35.284051+00:00
-- url     : https://prove2.me/theorems/197e6a28-f7e2-4fe0-adfd-2b20a3c0a968
-- title:
--   The OCB process has rank eight and obstruction five
-- statement:
--   All systems have positive finite dimensions and fixed computational bases. Choi operators are unnormalized and input first. A valid process maps every pair of local CPTP maps, with arbitrary ancillary input and output wires, to a CPTP map. Purity tests every compatible pair of local unitaries with those same ancillary extensions.
--
--   Let all four laboratory wires be qubits, with trivial $P,F$, and order Pauli words as $A_I A_O B_I B_O$. Write $I,X,Y,Z$ for the identity and usual Pauli matrices. Define
--
--   $$W_{\mathrm{OCB}}=\frac14\left[I^{\otimes4}+\frac{IZZI+ZIXZ}{\sqrt2}\right].$$
--
--   This is a valid process, and
--
--   $$\operatorname{rank}W_{\mathrm{OCB}}=8,\qquad\exists\text{ spectral and kernel-basis choices with }d_{\max}(W_{\mathrm{OCB}})=5,\qquad W_{\mathrm{OCB}}\text{ is not purifiable}.$$
--
--   The number five is the exact algebraic assertion reported by the source's numerical calculation. The existential choice does not claim the number is independent of all eigensolver bases. No maximal causal-inequality violation is asserted here.
-- source:
--   A purification postulate for quantum mechanics with indefinite causal order, arXiv:1611.08535v4, PDF p. 7, §6, Eq.(35)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P46

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Intake100.P46

/-- PDF p.7, §6, Eq.(35): the exact reported rank and obstruction, and nonpurifiability.
The spectral and kernel choices witnessing the reported numerical obstruction are existential;
this does not assert every eigensolver basis gives the number five. -/
theorem ocb_notPurifiable :
    IsValidProcess ocbProcess ∧ Matrix.rank ocbProcess = 8 ∧
    (∃ (e : SupportSpectrum (d := qubitLaboratories) ocbProcess)
      (b : KernelBasisData e) (s : CompressionSpectrum b), testBound s = 5) ∧
    ¬ IsPurifiable (d := qubitLaboratories) ocbProcess := by sorry

end QAlgorithms.Papers.Independent.Intake100.P46

end
