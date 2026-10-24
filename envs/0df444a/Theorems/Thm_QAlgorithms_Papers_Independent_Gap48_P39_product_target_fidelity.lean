-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P39_product_target_fidelity
-- name    : QAlgorithms.Papers.Independent.Gap48.P39.product_target_fidelity
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T05:20:23.956978+00:00
-- url     : https://prove2.me/theorems/05c2a9da-cd9a-4d2a-b6ff-46415b3fbed5
-- title:
--   Lemma 5: product-target fidelity from a pure marginal
-- statement:
--   Let $\rho^{AB}$ be a normalized density matrix on positive-dimensional finite systems, let $|\psi\rangle^A$ be a unit vector, and let $\sigma^B$ be any normalized density matrix. With $\rho^A,\rho^B$ the actual partial traces,
--
--   $$F(\rho^{AB},\psi^A\otimes\sigma^B)\ge1-3\bigl(1-F(\psi^A,\rho^A)\bigr)-\|\rho^B-\sigma^B\|_1.$$
--
--   Here $\psi^A=|\psi\rangle\langle\psi|$, $F$ is squared Uhlmann fidelity, and $\|\cdot\|_1$ is the full trace norm. The lower bound can be negative and is not clamped. This controls joint fidelity to a product target from a pure marginal and the other marginal's trace-norm error.
-- source:
--   Quantum broadcast channels, arXiv:quant-ph/0603098v2, PDF p. 11, Lemma 5: product-target fidelity from a pure marginal

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P39

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Gap48.P39

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P03 (PureEnsemble)

open QAlgorithms.Papers.Independent.Claimed50.P08 (cqBlocks holevoInfo)

open QAlgorithms.Papers.Independent.Dependency50.P19 (both epr mutualInformation marginalRA marginalRB)

open QAlgorithms.Papers.Independent.Information100.P58 (Distribution)

open QAlgorithms.Papers.Independent.Information100.P67 (squaredFidelity conditionalEntropy groupedChannelPower)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C X T E : Type}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype C] [DecidableEq C] [Fintype X] [DecidableEq X]

variable [Fintype T] [DecidableEq T] [Fintype E] [DecidableEq E]

/-- Lemma 5, PDF pp.11–12: squared fidelity, no square root on the factor 3;
the lower bound may be negative and is not clamped. -/
theorem product_target_fidelity [Nonempty A] [Nonempty B]
    (rho : Op (A × B)) (hr : IsDensityMatrix rho)
    (psi : EuclideanSpace ℂ A) (hp : IsState psi) (sigma : Op B) (hs : IsDensityMatrix sigma) :
    1 - 3 * (1 - squaredFidelity (pureDensity psi) (traceRight rho)) -
      traceNorm (traceLeft rho - sigma) ≤
      squaredFidelity rho (Matrix.kronecker (pureDensity psi) sigma) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P39

end
