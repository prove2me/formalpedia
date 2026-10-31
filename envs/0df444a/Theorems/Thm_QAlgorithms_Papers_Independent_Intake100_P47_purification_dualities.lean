-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P47_purification_dualities
-- name    : QAlgorithms.Papers.Independent.Intake100.P47.purification_dualities
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:26:05.15362+00:00
-- url     : https://prove2.me/theorems/b1f0b734-2208-48db-a9f2-26e7d25a047c
-- title:
--   Lemma 6: Three purification dualities
-- statement:
--   All Hilbert spaces are finite dimensional and nonzero. States are positive semidefinite operators of trace one, logarithms are natural, and $\rho\ll\sigma$ means inclusion of supports. Write $D_\alpha$ and $\widetilde D_\alpha$ for the Petz and sandwiched divergences, respectively, with generalized inverse powers on support and orders $0,1,\infty$ defined by limits. For a state $\rho_{AB}$ and a positive reference $\tau_A$ covering $\rho_A$, write $I_\alpha(\rho\|\tau)=\inf_{\sigma_B\in\mathcal S(B)}D_\alpha(\rho\|\tau\otimes\sigma_B)$ and $\widetilde I_\alpha$ for the analogous sandwiched quantity. Let $\rho_{AB}$ be a state, $\tau_A\ge0$ cover $\rho_A$, and $\rho_{ABC}$ be any normalized pure purification. Then
--   $$\widetilde I_\alpha(\rho_{AB}\|\tau_A)=-\widetilde I_\beta(\rho_{AC}\|\tau_A^{-1}),\quad \alpha,\beta\in[1/2,\infty),\quad\alpha^{-1}+\beta^{-1}=2,$$
--   $$I_\alpha(\rho_{AB}\|\tau_A)=-\widetilde D_{1/\alpha}(\rho_{AC}\|\tau_A^{-1}\otimes\rho_C),\quad 0\le\alpha<\infty,$$
--   $$D_\alpha(\rho_{AB}\|\tau_A\otimes\rho_B)=-D_\beta(\rho_{AC}\|\tau_A^{-1}\otimes\rho_C),\quad \alpha,\beta\in[0,2],\quad\alpha+\beta=2.$$
--   The first equation has finite orders; the second uses order infinity at $\alpha=0$. The inverse of $\tau_A$ is on its support. These identities transfer information statements to complementary systems; unnormalized references may give negative values.
-- source:
--   Correlation Detection and an Operational Interpretation of the Renyi Mutual Information, arXiv:1408.6894v5, PDF p. 9, Lemma 6: Three purification dualities

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P47

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P47

open scoped BigOperators Matrix ComplexOrder ComplexConjugate Topology

open Filter QAlgorithms

open QAlgorithms.Papers.Independent.Information100.P22 (Op mixed)

open QAlgorithms.Papers.Independent.Information100.P60 (copies)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms.Papers.Independent.Dependency50.P28 (SupportLE pinch logNonnegativeExtended)

open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy IsSupported)

open QAlgorithms.Papers.Independent.Bridge50.P49 (groupedProduct)

open QAlgorithms.Papers.Independent.Claimed50.P12 (DiagonalIn)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C D I J : Type}

variable [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype I] [Fintype J]

variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]

variable [DecidableEq I] [DecidableEq J]

/-- arXiv:1408.6894v5, PDF p.9, Lemma 6, all three purification dualities.
The first range contains finite real orders only; the second includes alpha=0
with beta=infinity. Inversion of tau is on its support. -/
theorem purification_dualities [Nonempty A] [Nonempty B] [Nonempty C]
    (rho : Op (A × B)) (tau : Op A) (hr : IsDensityMatrix rho)
    (ht : tau.PosSemidef) (hS : SupportLE (traceRight rho) tau)
    (psi : EuclideanSpace ℂ ((A × B) × C)) (hp : IsState psi)
    (hpur : traceRight (pureDensity psi) = rho) :
    (∀ a b : ℝ, 1/2 ≤ a → 1/2 ≤ b → a⁻¹ + b⁻¹ = 2 →
      generalizedInformation true (a : RenyiOrder) rho tau = -generalizedInformation true (b : RenyiOrder) (pureAC psi) (supportPower tau (-1))) ∧
    (∀ a : ℝ, 0 ≤ a → generalizedInformation false (a : RenyiOrder) rho tau =
      -completedRenyiDivergence true (inverseRenyiOrder a) (pureAC psi) (Matrix.kronecker (supportPower tau (-1)) (traceLeft (pureAC psi)))) ∧
    (∀ a b : ℝ, 0 ≤ a → a ≤ 2 → 0 ≤ b → b ≤ 2 → a+b = 2 →
      completedRenyiDivergence false (a : RenyiOrder) rho (Matrix.kronecker tau (traceLeft rho)) =
      -completedRenyiDivergence false (b : RenyiOrder) (pureAC psi) (Matrix.kronecker (supportPower tau (-1)) (traceLeft (pureAC psi)))) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P47

end
