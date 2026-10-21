-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P18_optimal_universal_not
-- name    : QAlgorithms.Papers.Independent.Support21.P18.optimal_universal_not
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T04:46:35.623975+00:00
-- url     : https://prove2.me/theorems/d62a1a5e-8917-4404-b5a1-abd2ce67c8ff
-- title:
--   Optimal universal NOT error
-- statement:
--   Let $N\ge1$ and let $\mathcal H_N^+$ be the symmetric subspace of $(\mathbb C^2)^{\otimes N}$, represented in its normalized occupation basis of dimension $N+1$. For a unit qubit vector $\psi$, write $\sigma_\psi=|\psi\rangle\langle\psi|$ and $\psi^N=\psi^{\otimes N}$. For a completely positive trace-preserving map $T:\mathcal B(\mathcal H_N^+)\to\mathcal B(\mathbb C^2)$ define $\Delta(T)=\max_{\|\psi\|=1}\operatorname{Tr}[\sigma_\psi T(|\psi^N\rangle\langle\psi^N|)]$.
--
--   Let $d\phi$ be normalized invariant pure-qubit measure and construct
--   $$
--   T_N(\rho)=\int (N+1)\langle\phi^N|\rho|\phi^N\rangle\,(I-|\phi\rangle\langle\phi|)\,d\phi.
--   $$
--   Then $T_N$ is a physical CPTP map and
--   $$
--   \Delta(T_N)=\frac1{N+2}\le\Delta(T)\quad\text{for every CPTP }T.
--   $$
--   The overlap set for every such competitor is nonempty and bounded above. The resulting worst-case complement fidelity is $1-\Delta(T_N)=(N+1)/(N+2)$.
--
--   This is optimality among all physical gates on the entire symmetric input space; covariance is a consequence of a separate reduction.
-- source:
--   Optimal Manipulations with Qubits: Universal NOT Gate, arXiv:quant-ph/9901053v1, PDF p. 3, Theorem (unnumbered), PDF p.3: optimal universal NOT error

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P18

noncomputable section

namespace QAlgorithms.Papers.Independent.Support21.P18

open MeasureTheory Filter

open scoped ComplexConjugate Matrix ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- PDF p.3, unnumbered Theorem, proved on p.4: the explicitly integrated
measurement scenario is an optimizer among ALL CPTP symmetric-input gates.
Covariance is not assumed of competitors. N=0 is outside the source regime. -/
theorem optimal_universal_not (N : ℕ) (hN : 1 ≤ N) :
    IsChannel (measurementNot N) ∧
    notError N (measurementNot N) = 1 / ((N : ℝ) + 2) ∧
    (∀ T : Superop (SymmetricBasis N) (Fin 2), IsChannel T →
      BddAbove (errorValues N T) ∧ (errorValues N T).Nonempty ∧
      1 / ((N : ℝ) + 2) ≤ notError N T) ∧
    1 - notError N (measurementNot N) = ((N : ℝ) + 1) / (N + 2) := by sorry

end QAlgorithms.Papers.Independent.Support21.P18

end
