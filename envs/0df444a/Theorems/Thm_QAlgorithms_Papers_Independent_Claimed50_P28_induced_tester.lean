-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P28_induced_tester
-- name    : QAlgorithms.Papers.Independent.Claimed50.P28.induced_tester
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:16:02.020143+00:00
-- url     : https://prove2.me/theorems/8412f659-c984-48f3-80b2-072d81e4c555
-- title:
--   Physical setups induce tester densities with the same statistics
-- statement:
--   Let the input and output dimensions be arbitrary positive integers, and let the ancillary dimension equal the input dimension. Prepare a density matrix $\rho$ on input $\otimes$ ancilla and measure output $\otimes$ ancilla with a normalized positive POVM density $P_x$. In fixed bases define the output-first tester density by
--
--   $$\Pi_x[(u,a),(v,b)]=\sum_{r,s}\rho[(b,r),(a,s)]P_x[(u,s),(v,r)].$$
--
--   Each $\Pi_x$ is positive, and its integral is $I_{\rm out}\otimes(\operatorname{Tr}_A\rho)^T$, whose second factor is a density matrix. For every completely positive trace-nonincreasing operation $T$, with unnormalized output-first Choi matrix $R_T$, the statistics agree exactly:
--
--   $$\operatorname{Tr}[(T\otimes I_A)(\rho)P_x]=\operatorname{Tr}[R_T\Pi_x].$$
--
--   This is the forward setup-to-tester reduction. It retains subnormalized success statistics and does not use the externally cited converse realization.
-- source:
--   Optimal quantum tomography for states, measurements, and transformations, arXiv:0806.1172v1, PDF p. 2, (11)–(15)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P28

noncomputable section

open MeasureTheory

open scoped BigOperators ComplexConjugate ComplexOrder Matrix Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Claimed50.P28

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted aliases/pairing; unrelated short-name collisions are not reused.

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Frontier18.P17 (hs)

/-- PDF p.2, (11)–(15): a normalized preparation and POVM induce a physical tester,
with exactly the original, possibly subnormalized, operation statistics. -/
theorem induced_tester {di do_ : ℕ} (hi : 0 < di) (ho : 0 < do_)
    {X : Type*} [MeasurableSpace X] (mu : Measure X)
    (rho : Op (Fin di × Fin di)) (P : X → Op (Fin do_ × Fin di))
    (hrho : QAlgorithms.IsDensityMatrix rho) (hP : IsPOVMDensity mu P) :
    IsTesterDensity mu (fun x => inducedTester rho (P x)) ∧
    (∫ x, inducedTester rho (P x) ∂mu) =
      Matrix.kronecker (1 : Op (Fin do_)) (traceInput rho).transpose ∧
    ∀ R : Op (Fin do_ × Fin di), IsOperation R → ∀ x,
      (applyWithAncilla R rho * P x).trace = (R * inducedTester rho (P x)).trace := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P28

end
