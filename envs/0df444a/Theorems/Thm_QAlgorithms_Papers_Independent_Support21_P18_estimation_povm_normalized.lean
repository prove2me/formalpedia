-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P18_estimation_povm_normalized
-- name    : QAlgorithms.Papers.Independent.Support21.P18.estimation_povm_normalized
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T04:48:14.310707+00:00
-- url     : https://prove2.me/theorems/13574c44-c69f-4455-a31e-a2e7b6739501
-- title:
--   Normalized coherent-state estimation POVM
-- statement:
--   For $N\ge1$, use the occupation basis of the symmetric $N$-qubit space $\mathcal H_N^+$ and normalized invariant pure-qubit measure $d\phi$. Define
--   $$
--   E_N(\phi)=(N+1)|\phi^{\otimes N}\rangle\langle\phi^{\otimes N}|,\qquad
--   p_N(\phi,\rho)=\operatorname{Tr}[E_N(\phi)\rho].
--   $$
--   The operator density is positive and integrable, and $\int E_N(\phi)\,d\phi=I_{\mathcal H_N^+}$. It defines a density POVM whose Born law is exactly $p_N(\phi,\rho)\,d\phi$. For every positive trace-one operator $\rho$ on $\mathcal H_N^+$, the real Born density is nonnegative, integrable, and has integral one. For unit $\phi,\psi$,
--   $$
--   p_N(\phi,|\psi^{\otimes N}\rangle\langle\psi^{\otimes N}|)=(N+1)|\langle\phi,\psi\rangle|^{2N}.
--   $$
--   This supplies the actual normalized measurement used by the measurement-and-preparation gate. The identity in the normalization formula acts on a space of dimension $N+1$.
-- source:
--   Optimal Manipulations with Qubits: Universal NOT Gate, arXiv:quant-ph/9901053v1, PDF p. 2, Measurement-based scenario, Eq.(3): normalized covariant estimation POVM

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P18

noncomputable section

namespace QAlgorithms.Papers.Independent.Support21.P18

open MeasureTheory Filter

open scoped ComplexConjugate Matrix ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- PDF p.2, Eq.(3) and its normalization paragraph: a normalized positive
coherent-state POVM on the symmetric space, not the full 2^N dimensional space.
The identity test operator in the source has trace N+1, not trace one. -/
theorem estimation_povm_normalized (N : ℕ) (hN : 1 ≤ N) :
    (∃ P : Measurements.DensityPOVM (SymmetricBasis N) (EuclideanSpace ℂ (Fin 2)),
      P.reference = pureLaw ∧ P.density = estimationEffect N ∧
      ∀ (rho : Matrix (SymmetricBasis N) (SymmetricBasis N) ℂ) (hrho : IsDensityMatrix rho),
        Measurements.bornLaw (Measurements.densityOperatorPOVM P) rho hrho =
          estimationLaw N rho) ∧
    Integrable (estimationEffect N) pureLaw ∧
    (∀ phi : EuclideanSpace ℂ (Fin 2), (estimationEffect N phi).PosSemidef) ∧
    (∫ phi, estimationEffect N phi ∂pureLaw) = 1 ∧
    (∀ rho : Matrix (SymmetricBasis N) (SymmetricBasis N) ℂ, IsDensityMatrix rho →
      Integrable (fun phi => (estimationWeight N rho phi).re) pureLaw ∧
      (∀ phi, 0 ≤ (estimationWeight N rho phi).re) ∧
      (∫ phi, (estimationWeight N rho phi).re ∂pureLaw) = 1 ∧
      estimationLaw N rho Set.univ = 1) ∧
    (∀ phi psi : EuclideanSpace ℂ (Fin 2), IsState phi → IsState psi →
      (estimationWeight N (pureDensity (symmetricQubitKet N psi)) phi).re =
        ((N : ℝ) + 1) * ‖inner ℂ phi psi‖ ^ (2 * N)) := by sorry

end QAlgorithms.Papers.Independent.Support21.P18

end
