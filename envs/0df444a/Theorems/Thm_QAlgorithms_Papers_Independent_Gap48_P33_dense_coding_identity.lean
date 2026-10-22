-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P33_dense_coding_identity
-- name    : QAlgorithms.Papers.Independent.Gap48.P33.dense_coding_identity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T04:43:43.239429+00:00
-- url     : https://prove2.me/theorems/e4b142be-b0ed-4eff-8dcd-6972133cf1ed
-- title:
--   dense-coding entropy identity
-- statement:
--   Prepare a finite classical label $C=j$ with probabilities $w_j$, conditional pure unit states $\psi_j$ on finite nonzero registers $R,Q$, and initially $I(R:Q)=I(R:C)=I(Q:C)=0$. After any CPTP channel on $Q$ alone, put $\sigma_j=(\mathrm{id}_R\otimes\mathcal N)(|\psi_j\rangle\langle\psi_j|)$. Then
--
--   $$I(R:Q'\mid C)=\sum_jw_j I(R:Q')_{\sigma_j}=I(RQ':C)=\chi(\{w_j,\sigma_j\}).$$
--
--   For the uniform four-Bell-state preparation and $\mathcal N_p$, $0\le p\le1$, the projective Bell measurement is a POVM attaining
--
--   $$\chi=2-H_2(p)-p\log_2 3,$$
--
--   and every finite POVM obtains at most this value. At $p=0$ the Bell outcome identifies the prepared label with certainty, yielding two classical bits using one transmitted qubit and the shared reference. The accessible-information equality is restricted to this commuting ensemble.
--
--   Here $H_2$ denotes binary Shannon entropy in bits, with $0\log 0=0$.
-- source:
--   On the von Neumann capacity of noisy quantum channels, arXiv:quant-ph/9609024v3, PDF p. 13, VI.A, (6.1)–(6.2): dense-coding entropy identity

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P33

namespace QAlgorithms.Papers.Independent.Gap48.P33

open scoped BigOperators Matrix ComplexConjugate

-- Reuse only definitions from the pinned accepted library; no imported theorem is used.

open QAlgorithms.Papers.Independent.Information100.P27 (shannon average labelInformation)

open QAlgorithms.Papers.Independent.Information100.P08 (canonicalPurification)

open QAlgorithms.Papers.Independent.Dependency50.P19 (mutualInformation first both)

open QAlgorithms.Papers.Independent.Dependency50.P24 (cqState)

open QAlgorithms.Papers.Independent.Dependency50.P45 (entropyExchange inputMutualInfo)

open QAlgorithms.Papers.Independent.Claimed50.P03 (pauliWeight wordSupport)

section FiniteRegisters

variable {A B C D R K J : Type}

variable [Fintype A] [Fintype B] [Fintype C] [Fintype D]

variable [Fintype R] [Fintype K] [Fintype J]

variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]

variable [DecidableEq R] [DecidableEq K] [DecidableEq J]

/-- PDF pp.12–13, (6.1)–(6.2): general entropy identity with the prepared ensemble's
three vanishing pairwise informations. Accessible-information equality is asserted
only for the commuting Bell/Pauli ensemble, with its attaining Bell measurement. -/
theorem dense_coding_identity
    [Nonempty R] [Nonempty A] [Nonempty B]
    (w : J → ℝ) (hw : ProbabilityWeights w)
    (psi : J → EuclideanSpace ℂ (R × A)) (hpsi : ∀ j, IsState (psi j))
    (hRQ : mutualInformation (average w (fun j => pureDensity (psi j))) = 0)
    (hRC : labelInformation w (fun j => traceRight (pureDensity (psi j))) = 0)
    (hQC : labelInformation w (fun j => traceLeft (pureDensity (psi j))) = 0)
    (N : Superop A B) (hN : IsChannel N) :
    let output := fun j => idTensorSuperop N (pureDensity (psi j))
    (∑ j, w j * mutualInformation (output j)) = mutualInformation (cqState w output) ∧
    mutualInformation (cqState w output) = labelInformation w output ∧
    (∀ p : ℝ, 0 ≤ p → p ≤ 1 →
      labelInformation (fun _ : Fin 4 => (1 / 4 : ℝ)) (bellOutputs p) =
        2 - binEntropy2 p - p * Real.logb 2 3 ∧
      IsPOVM bellMeasurement ∧
      measurementInformation (fun _ : Fin 4 => (1 / 4 : ℝ)) (bellOutputs p) bellMeasurement =
        2 - binEntropy2 p - p * Real.logb 2 3 ∧
      (∀ (m : ℕ) (M : Fin m → Matrix (Bool × Bool) (Bool × Bool) ℂ), IsPOVM M →
        measurementInformation (fun _ : Fin 4 => (1 / 4 : ℝ)) (bellOutputs p) M ≤
          2 - binEntropy2 p - p * Real.logb 2 3) ∧
      (∀ j l : Fin 4, effectProb (bellMeasurement l) (bellOutputs 0 j) =
        if l = j then 1 else 0)) := by sorry

end FiniteRegisters

end QAlgorithms.Papers.Independent.Gap48.P33
