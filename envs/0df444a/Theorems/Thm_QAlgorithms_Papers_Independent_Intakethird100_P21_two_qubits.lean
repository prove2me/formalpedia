-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P21_two_qubits
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P21.two_qubits
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:01:05.293027+00:00
-- url     : https://prove2.me/theorems/e8bcc658-1376-46a3-91b7-7da79fda0f54
-- title:
--   Two-qubit formulas with a common optimal ensemble
-- statement:
--   For two qubits and $0\le F\le1$, let $\rho_{2,F}=FP_2+(1-F)(I-P_2)/3$ be the isotropic density. Its I-concurrence and tangle are
--
--   $$
--   C(\rho_{2,F})=\max(0,2F-1),\qquad
--   \tau(\rho_{2,F})=\max(0,2F-1)^2.
--   $$
--
--   On $[1/2,1]$ the raw profiles satisfy $c_2(F)=2F-1$ and $q_2(F)=(2F-1)^2$. There exists one finite normalized pure-state decomposition attaining both mixed roofs, and every positive-weight member has pure concurrence $C(\rho_{2,F})$ and pure tangle $\tau(\rho_{2,F})$.
--
--   The concurrence corrects the source's printed sign typo. This special dimension has coincident tangle and squared mixed concurrence.
-- source:
--   I-concurrence and tangle for isotropic states, arXiv:quant-ph/0208002v1, PDF p. 10, §3.4.1, (3.37): two-qubit formulas and constant-tangle optimal ensembles

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P21

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P21

open scoped Matrix ComplexConjugate

open Filter

open QAlgorithms

open QAlgorithms.Papers.Independent.Information100.P03
  (PureEnsemble convexRoof pureConcurrence concurrence SchmidtData schmidtVector)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.10, (3.37): corrected concurrence is 2F-1 above 1/2;
the printed 1-2F gives -1 at F=1. Optimal ensembles are existential,
and every positive-weight component has the same pure cost. -/
theorem two_qubits (F : ℝ) (hF : F ∈ Set.Icc (0 : ℝ) 1) :
    tangle (isotropicDensityAtFidelity 2 F) = (if F ≤ 1/2 then 0 else (2*F-1)^2) ∧
    concurrence (isotropicDensityAtFidelity 2 F) = (if F ≤ 1/2 then 0 else 2*F-1) ∧
    (∀ F ∈ Set.Icc (1/2 : ℝ) 1, constrainedSchmidtTangle 2 F = (2*F-1)^2 ∧ rawC 2 F = 2*F-1) ∧
    (∃ e : PureEnsemble (Fin 2 × Fin 2), IsOptimalPureEnsemble pureTangle (isotropicDensityAtFidelity 2 F) e ∧
      IsOptimalPureEnsemble pureConcurrence (isotropicDensityAtFidelity 2 F) e ∧
      ∀ k, 0 < e.weight k → pureTangle (e.vector k) = tangle (isotropicDensityAtFidelity 2 F) ∧
        pureConcurrence (e.vector k) = concurrence (isotropicDensityAtFidelity 2 F)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P21

end
