-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P45_linearAverageInputConstraint
-- name    : QAlgorithms.Papers.Independent.Dependency50.P45.linearAverageInputConstraint
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T17:06:35.860683+00:00
-- url     : https://prove2.me/theorems/ca6ae5be-6b63-4e12-9595-17b2d29118ff
-- title:
--   §III: capacity formula under a linear average-input constraint
-- statement:
--   Let $\mathcal N:A\to B$ be a finite-dimensional memoryless CPTP map with nonzero input and output spaces. Fix a Hermitian input observable $G$ and real bound $S$, with at least one density matrix satisfying $\operatorname{Tr}(G\rho)\le S$. Let $C_E(\mathcal N;G,S)$ be operational entanglement-assisted classical capacity with unlimited prior EPR pairs, local CPTP encoding, collective decoding, no other communication, and every-message error vanishing uniformly. For each block the cost is averaged over its uniformly distributed Boolean messages and all input marginals. Then the maximum is attained and
--
--   $$C_E(\mathcal N;G,S)=\max_{\rho\text{ density},\ \operatorname{Tr}(G\rho)\le S}\bigl[H(\rho)+H(\mathcal N(\rho))-H((\operatorname{id}\otimes\mathcal N)\Phi_\rho)\bigr].$$
--
--   Here $\Phi_\rho$ is normalized and $H$ and the capacity are in bits. This imposes an average-density constraint, not a peak constraint or finite-support cutoff.
-- source:
--   Entanglement-assisted capacity of a quantum channel and the reverse Shannon theorem, arXiv:quant-ph/0106052v2, PDF p. 27, §III: capacity formula under a linear average-input constraint

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P45

noncomputable section

open scoped ComplexConjugate Matrix

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Dependency50.P45

attribute [local instance] Classical.propDecidable

open QAlgorithms.Papers.Independent.Information100.P08 (canonicalPurification)

open QAlgorithms.Papers.Independent.Information100.P76 (dampingChannel)

/-- PDF p.27: operational capacity maximizes over feasible average signaling densities. -/
theorem linearAverageInputConstraint {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]
    (N : Superop A B) (hN : IsChannel N) (G : Matrix A A ℂ)
    (hG : G.IsHermitian) (S : ℝ)
    (hfeasible : ∃ rho : Matrix A A ℂ, IsDensityMatrix rho ∧ (G * rho).trace.re ≤ S) :
    IsGreatest {v | ∃ rho : Matrix A A ℂ, IsDensityMatrix rho ∧
      (G * rho).trace.re ≤ S ∧ v = inputMutualInfo N rho}
      (constrainedCapacity N G S) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P45

end
