-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P46_opt_test_inconclusive
-- name    : QAlgorithms.Papers.Independent.Intake100.P46.opt_test_inconclusive
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:10:03.379998+00:00
-- url     : https://prove2.me/theorems/c0d5a873-9f69-4824-9422-093cedcc2a5e
-- title:
--   The Wopt purification test is inconclusive
-- statement:
--   All systems have positive finite dimensions and fixed computational bases. Choi operators are unnormalized and input first. A valid process maps every pair of local CPTP maps, with arbitrary ancillary input and output wires, to a CPTP map. Purity tests every compatible pair of local unitaries with those same ancillary extensions.
--
--   With four qubit laboratory wires, trivial $P,F$, and Pauli order $A_I A_O B_I B_O$, define
--
--   $$W_{\mathrm{opt}}=\frac14\left[I^{\otimes4}+\frac{ZIXZ}{\sqrt3}+\frac{\sqrt3-1}{3}(IXXI+IYYI+IZZI)\right].$$
--
--   This is a valid process with
--
--   $$\operatorname{rank}W_{\mathrm{opt}}=12,\qquad \exists\text{ spectral and kernel-basis choices with }d_{\max}(W_{\mathrm{opt}})=17\ge12.$$
--
--   Thus the strict inequality required by the nonpurifiability test does not hold for the reported choice. This states neither purifiability nor nonpurifiability. The exact obstruction value is the algebraic assertion reported by the source, without a claim of basis independence.
-- source:
--   A purification postulate for quantum mechanics with indefinite causal order, arXiv:1611.08535v4, PDF p. 7, §6, Eq.(37)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P46

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Intake100.P46

/-- PDF p.7, §6, Eq.(37): the reported test is inconclusive, with rank twelve and a
choice giving bound seventeen. No conclusion about purification is asserted. -/
theorem opt_test_inconclusive :
    IsValidProcess optProcess ∧ Matrix.rank optProcess = 12 ∧
    ∃ (e : SupportSpectrum (d := qubitLaboratories) optProcess)
      (b : KernelBasisData e) (s : CompressionSpectrum b),
      testBound s = 17 ∧ ¬ testBound s < (Matrix.rank optProcess : WithTop ℕ) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P46

end
