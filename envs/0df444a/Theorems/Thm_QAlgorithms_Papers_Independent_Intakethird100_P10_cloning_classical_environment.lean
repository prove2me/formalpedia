-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P10_cloning_classical_environment
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P10.cloning_classical_environment
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:46:00.854399+00:00
-- url     : https://prove2.me/theorems/5ff52f78-b381-4174-9fd4-fc788480894c
-- title:
--   The displayed cloning-environment states commute
-- statement:
--   Let $m\ge1$ be the number of clones, put $\Delta_m=m(m+1)/2$, and choose any orthonormal basis $\{|e_i\rangle\}_{i=0}^{m-1}$ of the environment. Construct the two displayed states
--
--   $$
--   \rho_0^E=\sum_{i=0}^{m-1}{i+1\over\Delta_m}|e_i\rangle\langle e_i|,\qquad
--   \rho_1^E=\sum_{i=0}^{m-1}{i+1\over\Delta_m}|e_{m-1-i}\rangle\langle e_{m-1-i}|.
--   $$
--
--   Both are positive trace-one matrices and they commute. The source's cited covariance identifies these as the complementary outputs for any orthonormal qubit input basis, allowing the common environment basis to depend on that input basis. The formal statement verifies the explicit output formulas in any common environment basis; it does not reconstruct the full cloning channel from two outputs.
-- source:
--   Polar codes for degradable quantum channels, arXiv:1109.5346v3, PDF p. 11, Appendix B, unnumbered cloning-channel classical-environment example

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P10

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P10

open scoped BigOperators Matrix ComplexConjugate

open Filter

-- Accepted definitions, without paper-local aliases.

open QAlgorithms.Papers.Independent.Information100.P58 (basisDensity)

open QAlgorithms.Papers.Independent.Information100.P67 (squaredFidelity)

open QAlgorithms.Papers.Independent.Claimed50.P48 (indexedKrausDilation)

/-- PDF p.11, Appendix B: the explicitly displayed outputs are states and commute
in every common environmental orthonormal basis. The cited covariance permits this
basis to depend on the chosen qubit input basis. m=0 is excluded; m=1 is allowed. -/
theorem cloning_classical_environment (m : ℕ) (hm : 0 < m)
    (basis : Matrix.unitaryGroup (Fin m) ℂ) :
    IsBinaryCQ (cloningEnvironment m basis) ∧
    Commute (cloningEnvironment m basis false) (cloningEnvironment m basis true) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P10

end
