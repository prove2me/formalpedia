-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P36_dephasingFunctionalAdditive
-- name    : QAlgorithms.Papers.Independent.Renew46.P36.dephasingFunctionalAdditive
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T22:12:46.968027+00:00
-- url     : https://prove2.me/theorems/1e0e9908-a960-44d8-8c54-f8d6e69ee8b4
-- title:
--   Lemma 7: additive dephasing supporting functional
-- statement:
--   For each of two finite generalized dephasing channels $\mathcal N_j$, fix normalized environment vectors $\phi_{j,i}$ in a finite nonzero environment and the dilation $|i\rangle\mapsto|i\rangle|\phi_{j,i}\rangle$. For $\lambda\geq1$ define
--
--   $$
--   f_\lambda(\mathcal N)=\max_{\{p_x,\rho_x\}}
--   \left[H\!\left(\sum_xp_x\Delta(\rho_x)\right)
--    +(\lambda-1)\sum_xp_xH(\Delta(\rho_x))
--    -\lambda\sum_xp_xH(\mathcal N^c(\rho_x))\right],
--   $$
--
--   where the maximum ranges over all finite probability ensembles of normalized input density matrices, $\Delta$ is complete dephasing in the preferred basis, and $\mathcal N^c$ is the fixed-dilation complementary channel. Entropies are in bits. Then
--
--   $$
--   f_\lambda(\mathcal N_1\otimes\mathcal N_2)
--   =f_\lambda(\mathcal N_1)+f_\lambda(\mathcal N_2).
--   $$
--
--   The product-channel optimization allows arbitrary joint, including entangled, input densities; it is not restricted to product ensembles. This additivity controls the supporting functionals of the full simultaneous region. The Lean statement explicitly asserts that each of the two individual-channel suprema and the product-channel supremum is attained by a finite normalized input ensemble, as well as the displayed additivity equality.
-- source:
--   The capacity of a quantum channel for simultaneous transmission of classical and quantum information, arXiv:quant-ph/0311131v3, PDF p. 14, Lemma 7: additive dephasing supporting functional

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P36

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Renew46.P36

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P08 (Ensemble canonicalPurification)

open QAlgorithms.Papers.Independent.Dependency50.P07 (Typical)

open QAlgorithms.Papers.Independent.Information100.P27 (qubitDephasing)

open QAlgorithms.Papers.Independent.Dependency50.P41 (maximallyEntangled)

open QAlgorithms.Papers.Independent.Claimed50.P20 (DynamicPureEnsemble pureOutputs cqHolevoBits conditionalCoherent)

open QAlgorithms.Papers.Independent.Information100.P67
  (IsDegradable receiverChannel complementaryChannel maximumCoherentInformation squaredFidelity)

open QAlgorithms.Papers.Independent.Information100.P76 (maximallyMixed)

open QAlgorithms.Papers.Independent.Information100.P80 (quantumCapacity)

open QAlgorithms.Papers.Independent.Next46.P40
  (dephasingIsometry generalizedDephasing diagonalPart)

variable {A B E A1 A2 E1 E2 : Type}

variable [Fintype A] [Fintype B] [Fintype E]

variable [Fintype A1] [Fintype A2] [Fintype E1] [Fintype E2]

/-- Lemma 7, PDF p.14: additive dephasing supporting functional, lambda>=1.
The product optimization includes arbitrary joint/entangled input densities.
All three finite-ensemble suprema are attained, as required by the source's maxima.
The proof's conditional-entropy comparison has a sign typo; its intended direction
is fixed by the following negative-lambda estimate. -/
theorem dephasingFunctionalAdditive
    [Nonempty A1] [Nonempty A2] [Nonempty E1] [Nonempty E2]
    (env1 : A1 → EuclideanSpace ℂ E1) (env2 : A2 → EuclideanSpace ℂ E2)
    (h1 : ∀ a, ‖env1 a‖ = 1) (h2 : ∀ a, ‖env2 a‖ = 1)
    (lambda : ℝ) (hlambda : 1 ≤ lambda) :
    dephasingFunctional (productEnvironment env1 env2) lambda =
      dephasingFunctional env1 lambda + dephasingFunctional env2 lambda ∧
    (∃ P : Ensemble A1,
      dephasingFunctional env1 lambda =
        vnEntropy (∑ x, (P.prob x : ℂ) • diagonalPart (P.state x)) +
          (lambda - 1) * (∑ x, P.prob x * vnEntropy (diagonalPart (P.state x))) -
          lambda * (∑ x, P.prob x *
            vnEntropy (complementaryChannel (dephasingIsometry env1) (P.state x)))) ∧
    (∃ P : Ensemble A2,
      dephasingFunctional env2 lambda =
        vnEntropy (∑ x, (P.prob x : ℂ) • diagonalPart (P.state x)) +
          (lambda - 1) * (∑ x, P.prob x * vnEntropy (diagonalPart (P.state x))) -
          lambda * (∑ x, P.prob x *
            vnEntropy (complementaryChannel (dephasingIsometry env2) (P.state x)))) ∧
    (∃ P : Ensemble (A1 × A2),
      dephasingFunctional (productEnvironment env1 env2) lambda =
        vnEntropy (∑ x, (P.prob x : ℂ) • diagonalPart (P.state x)) +
          (lambda - 1) * (∑ x, P.prob x * vnEntropy (diagonalPart (P.state x))) -
          lambda * (∑ x, P.prob x *
            vnEntropy (complementaryChannel
              (dephasingIsometry (productEnvironment env1 env2)) (P.state x)))) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P36

end
