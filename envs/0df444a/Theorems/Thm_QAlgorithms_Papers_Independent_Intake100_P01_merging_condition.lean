-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P01_merging_condition
-- name    : QAlgorithms.Papers.Independent.Intake100.P01.merging_condition
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:48:56.209692+00:00
-- url     : https://prove2.me/theorems/c2a92263-7e47-4fb5-9fe3-88b83b786ba7
-- title:
--   Proposition 3 (Merging condition)
-- statement:
--   Let $|\psi\rangle_{ABR}$ be a unit vector on finite nonzero registers, and let $\{P_j:A\to\mathbb C^L\}$ be a complete finite Kraus measurement with $L\ge1$. For outcome $j$, let $p_j$ and $\rho^j_{A_1R}$ be its Born probability and normalized reduced state, and let $\rho_R$ be the original reference marginal. Put $\tau_L=I/L$. If $\epsilon\ge0$ and
--   $$Q=\sum_jp_j\|\rho^j_{A_1R}-\tau_L\otimes\rho_R\|_1\le\epsilon,$$
--   Bob has outcome-dependent isometries completing a one-way LOCC protocol with no initial entanglement and output Schmidt rank $L$, of cost $-\log_2L$. Its complete output $\sigma$, including the untouched reference, satisfies
--   $$F(\sigma,\Phi_L\otimes\psi_{B'BR})\ge1-\epsilon,\qquad \|\sigma-\Phi_L\otimes\psi_{B'BR}\|_1\le2\sqrt\epsilon.$$
--   Here $F$ is squared fidelity and the norm is unhalved. This is the one-shot decoupling criterion used to complete merging.
--
--   **Formalization Note** Weighted errors are computed directly from unnormalized branches, so zero-probability outcomes require no division.
-- source:
--   Quantum state merging and negative information, arXiv:quant-ph/0512247v1, PDF p. 5, Proposition 3 (Merging condition)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P01

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P01

open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise

open MeasureTheory

open QAlgorithms.Papers.Independent.Gap20.P11 (IsLOCC productApply finTransport referenceInformation)

open QAlgorithms.Papers.Independent.Bridge50.P40
  (RankMergingCode OneWayMergingCode mergingFidelity SourceProtocolAchievable)

open QAlgorithms.Papers.Independent.Dependency50.P19
  (first marginalRA marginalRB motherTarget motherOutput sourceCopies swap mutualInformation)

open QAlgorithms.Papers.Independent.Information100.P67 (conditionalEntropy)

open QAlgorithms.Papers.Independent.Information100.P32 (purity)

open QAlgorithms.Papers.Independent.Advance50.P29 (weakTypicalProjector)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.5--6, Proposition 3. Printed (14) omits p_j for normalized branches;
changed to the sum of unnormalized branches, as required by (6),(13),(15).
The two error metrics are exactly (15) and (16). -/
theorem merging_condition {A B R J : Type}
    [Fintype A] [Fintype B] [Fintype R] [Fintype J]
    [Nonempty A] [Nonempty B] [Nonempty R] [Nonempty J]
    (psi : EuclideanSpace ℂ (R × (A × B))) (hpsi : IsState psi)
    (L : ℕ) (hL : 0 < L) (P : J → Matrix (Fin L) A ℂ)
    (hP : IsKrausFamily P) (eps : ℝ) (heps : 0 ≤ eps)
    (hQ : mergingDecouplingError (pureDensity psi) P ≤ eps) :
    CompletedMerging (pureDensity psi) P eps := by sorry

end QAlgorithms.Papers.Independent.Intake100.P01

end
