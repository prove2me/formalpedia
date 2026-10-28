-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P15_proposition5_quantumCoupling
-- name    : QAlgorithms.Papers.Independent.Dependency50.P15.proposition5_quantumCoupling
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T16:23:43.367978+00:00
-- url     : https://prove2.me/theorems/93b8f117-9e0d-479e-832b-f06b340d079b
-- title:
--   Proposition 5: quantum coupling with purifications
-- statement:
--   Fix an orthonormal basis of a nonzero finite-dimensional complex Hilbert space $A$. Let $\rho,\sigma$ be positive operators of trace one, and let $\varepsilon\ge0$ satisfy $T(\rho,\sigma)=\frac12\|\rho-\sigma\|_1\le\varepsilon$. There exist unit vectors $\phi,\psi$, a vector $\vartheta$ with $\|\vartheta\|\le1$, and a density operator $\Theta$, all on $A_1\otimes A_2=A\otimes A$, simultaneously satisfying
--
--   $$\phi^{A_1}=\rho,\quad\phi^{A_2}=\rho^T,\quad\psi^{A_1}=\sigma,\quad\psi^{A_2}=\sigma^T,$$
--   $$\operatorname{Tr}_{A_2}|\vartheta\rangle\langle\vartheta|\le\rho,\quad\operatorname{Tr}_{A_1}|\vartheta\rangle\langle\vartheta|\le\sigma^T,\quad |\langle\psi|\vartheta\rangle|,|\langle\phi|\vartheta\rangle|\ge1-\varepsilon,$$
--   $$\Theta^{A_1}=\rho,\quad\Theta^{A_2}=\psi^{A_2}=\sigma^T,\quad F(\psi,\Theta),F(\phi,\Theta)\ge1-\varepsilon.$$
--
--   Here vector marginals mean marginals of their pure densities, transpose uses the fixed basis, and $F$ is root fidelity. The common witnesses give a quantum coupling compatible with both purifications.
-- source:
--   Tight uniform continuity bounds for quantum entropies: conditional entropy, relative entropy distance and energy constraints, arXiv:1507.07775v6, PDF p. 4, Proposition 5: quantum coupling with purifications

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P15

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Dependency50.P15

open QAlgorithms.Papers.Independent.Information100.P08 (bellVector)

/-- Proposition 5, PDF pp.4–5: all purification, domination, overlap and consequent
coupling conditions hold for the SAME witnesses. The second coupling marginal is sigma^T.
Fidelity is root fidelity. No upper bound on epsilon is imposed. -/
theorem proposition5_quantumCoupling {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (rho sigma : Matrix I I ℂ) (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) (hclose : traceDistance rho sigma ≤ epsilon) :
    ∃ phi psi theta : EuclideanSpace ℂ (I × I),
    ∃ Theta : Matrix (I × I) (I × I) ℂ,
      ‖phi‖ = 1 ∧ ‖psi‖ = 1 ∧ ‖theta‖ ≤ 1 ∧
      traceRight (pureDensity phi) = rho ∧ traceLeft (pureDensity phi) = rho.transpose ∧
      traceRight (pureDensity psi) = sigma ∧ traceLeft (pureDensity psi) = sigma.transpose ∧
      (rho - traceRight (pureDensity theta)).PosSemidef ∧
      (sigma.transpose - traceLeft (pureDensity theta)).PosSemidef ∧
      1 - epsilon ≤ ‖inner ℂ psi theta‖ ∧ 1 - epsilon ≤ ‖inner ℂ phi theta‖ ∧
      IsDensityMatrix Theta ∧ traceRight Theta = rho ∧
      traceLeft Theta = traceLeft (pureDensity psi) ∧
      1 - epsilon ≤ rootFidelity (pureDensity psi) Theta ∧
      1 - epsilon ≤ rootFidelity (pureDensity phi) Theta := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P15

end
