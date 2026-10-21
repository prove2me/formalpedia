-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P18_measurement_output
-- name    : QAlgorithms.Papers.Independent.Support21.P18.measurement_output
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T04:48:56.78499+00:00
-- url     : https://prove2.me/theorems/c54db100-a739-44a2-a71b-30cc0ab362d5
-- title:
--   Measurement-based outputs and arbitrary multiplicity
-- statement:
--   Let $N,M\ge1$, let $\rho$ be an input operator on the symmetric $N$-qubit space, and set $p_N(\phi,\rho)=(N+1)\langle\phi^{\otimes N}|\rho|\phi^{\otimes N}\rangle$. With normalized invariant pure-qubit measure, construct
--   $$
--   T_{N,M}(\rho)=\int p_N(\phi,\rho)(I-|\phi\rangle\langle\phi|)^{\otimes M}\,d\phi.
--   $$
--   This map is CPTP. Write $T_N$ for its one-qubit version, and $\sigma=|\psi\rangle\langle\psi|$ for a unit input vector. On $\rho=|\psi^{\otimes N}\rangle\langle\psi^{\otimes N}|$, every individual output and the single output of $T_N$ have density
--   $$
--   \tau_N(\psi)=\frac N{N+2}(I-\sigma)+\frac1{N+2}I.
--   $$
--   Each complement fidelity is $(N+1)/(N+2)$, independent of the output site, $M$, and $\psi$, and $\Delta(T_N)=1/(N+2)$. This fidelity is strictly less than one for finite $N$; for each fixed unit $\psi$, $\tau_N(\psi)\to I-\sigma$ as $N\to\infty$.
--
--   The single estimate is shared by all prepared outputs, so the integral specifies their joint state and permits correlations.
--
--   Here $\Delta(T_N)$ is the maximum, over all unit pure inputs, of the overlap of the single-qubit output with the original input state.
-- source:
--   Optimal Manipulations with Qubits: Universal NOT Gate, arXiv:quant-ph/9901053v1, PDF p. 2, Measurement-based scenario, Eqs.(4)-(6): output and arbitrary output multiplicity

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P18

noncomputable section

namespace QAlgorithms.Papers.Independent.Support21.P18

open MeasureTheory Filter

open scoped ComplexConjugate Matrix ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- PDF pp.2-3, Eqs.(4)-(6): any positive number of outputs may share a common
estimate, with the stated individual fidelity. The joint output may be correlated.
Finite-N strictness and convergence to the perfect complement are included. -/
theorem measurement_output (N M : ℕ) (hN : 1 ≤ N) (hM : 1 ≤ M) :
    IsChannel (measurementMany N M) ∧
    notError N (measurementNot N) = 1 / ((N : ℝ) + 2) ∧
    (∀ psi : EuclideanSpace ℂ (Fin 2), IsState psi →
      measurementNot N (pureDensity (symmetricQubitKet N psi)) = complementOutput N psi ∧
      ∀ i : Fin M,
        siteReduction (measurementMany N M (pureDensity (symmetricQubitKet N psi))) i =
          complementOutput N psi ∧
        effectProb (orthogonalDensity psi)
          (siteReduction (measurementMany N M (pureDensity (symmetricQubitKet N psi))) i) =
          ((N : ℝ) + 1) / (N + 2)) ∧
    ((N : ℝ) + 1) / (N + 2) < 1 ∧
    (∀ psi : EuclideanSpace ℂ (Fin 2), IsState psi →
      Tendsto (fun n : ℕ => complementOutput n psi) atTop (nhds (orthogonalDensity psi))) := by sorry

end QAlgorithms.Papers.Independent.Support21.P18

end
