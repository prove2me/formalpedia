-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P12_fullSchmidtRank_target
-- name    : QAlgorithms.Papers.Independent.Advance50.P12.fullSchmidtRank_target
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:18:18.083321+00:00
-- url     : https://prove2.me/theorems/b2ac6e1e-9572-4ca8-9f71-00ad3c6e1459
-- title:
--   Remark 1 / (34): full-Schmidt-rank target extension
-- statement:
--   All registers are finite-dimensional complex Hilbert spaces of positive dimension, represented in arbitrary orthonormal bases. States are positive semidefinite operators of trace one. All logarithms are binary, and $F(\rho,\sigma)=\|\sqrt\rho\sqrt\sigma\|_1$ denotes root fidelity. Conditional min-entropy optimizes the operator-order definition over every normalized reference state; conditional max-entropy is defined by purification duality.
--
--   Let $\rho_{AB}$ be any bipartite state and let $|\Psi_{AA'}\rangle$ be a normalized full-Schmidt-rank vector with $A'\cong A$. Its actual marginal $\tau_A=\operatorname{tr}_{A'}|\Psi\rangle\langle\Psi|$ is positive definite. Define $D_\infty(R\|S)=\inf\{\lambda\in\mathbb R:R\le2^\lambda S\}$. Then
--   $$\min_{\sigma_B\text{ state}}D_\infty(\rho_{AB}\|\tau_A^{-1}\otimes\sigma_B)=\log_2\max_{\mathcal F:B\to A'}F((\mathrm{id}_A\otimes\mathcal F)(\rho_{AB}),|\Psi\rangle\langle\Psi|)^2.$$
--   Both extrema are attained, and the maps are all CPTP operations. The inverse is an actual matrix inverse, the logarithm has a positive sign, and there is no dimension multiplier. This extends the singlet-fraction identity, including the maximally entangled target as a special case.
-- source:
--   The operational meaning of min- and max-entropy, arXiv:0807.1338v2, PDF p. 9, Remark 1 / (34)

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P12

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P12

open QAlgorithms

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P07 (CQData cqDensity)

open QAlgorithms.Papers.Independent.Dependency50.P35 (maxRelative elog marginalAB)

open QAlgorithms.Papers.Independent.Information100.P67 (conditionalMinEntropy)

open QAlgorithms.Papers.Independent.Renew46.P35 (traceAdjoint)

open QAlgorithms.Papers.Independent.Support50.P23 (exp2Extended independentProduct)

variable {A B C D X : Type}

variable [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype X]

variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D] [DecidableEq X]

/-- PDF p.9, Remark 1 / (34): full-Schmidt-rank target extension.
The computed target marginal is positive definite, hence its matrix inverse is
an actual inverse. The RHS has positive log and no dimension multiplier. -/
theorem fullSchmidtRank_target [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (hrho : IsDensityMatrix rho)
    (psi : EuclideanSpace ℂ (A × A)) (hpsi : ‖psi‖ = 1)
    (hfull : (traceRight (pureDensity psi)).PosDef) :
    let tau := traceRight (pureDensity psi)
    let value := sInf {v : EReal | ∃ sigma : Matrix B B ℂ,
      IsDensityMatrix sigma ∧ v = maxRelative rho (Matrix.kronecker tau⁻¹ sigma)}
    value = elog (targetOverlap rho psi) ∧
    (∃ sigma : Matrix B B ℂ, IsDensityMatrix sigma ∧
      maxRelative rho (Matrix.kronecker tau⁻¹ sigma) = value) ∧
    (∃ f : Superop B A, IsChannel f ∧
      rootFidelity (idTensorSuperop f rho) (pureDensity psi) ^ 2 = targetOverlap rho psi) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P12

end
