-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P33_loss_fidelity_fano
-- name    : QAlgorithms.Papers.Independent.Gap48.P33.loss_fidelity_fano
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T04:37:49.356721+00:00
-- url     : https://prove2.me/theorems/1a87b613-9eee-4e8e-8d00-1da47587032b
-- title:
--   quantum loss–fidelity Fano bound
-- statement:
--   Let $\psi_{RQ}$ be a unit vector, $\rho_Q=\operatorname{Tr}_R|\psi\rangle\langle\psi|$, and let noise $\mathcal N:Q\to Q_1$ be followed by CPTP recovery $\mathcal M:Q_1\to Q$. The final signal is identified with the initial signal. Put $d=\dim R\dim Q$ and $F=\langle\psi|(\mathrm{id}_R\otimes(\mathcal M\circ\mathcal N))(|\psi\rangle\langle\psi|)|\psi\rangle$. For $d\ge2$,
--
--   $$L_{12}\le2\bigl[H_2(F)+(1-F)\log_2(d-1)\bigr],\qquad L_1\le2\bigl[H_2(F)+(1-F)\log_2(d-1)\bigr].$$
--
--   Here $L_{12}$ is the composite loss and $L_1$ the noise loss, both relative to $\rho_Q$; the second inequality follows from (3.37). If $d=1$, $F=1$ and $L_1=L_{12}=0$. This relates loss to squared purification fidelity.
--
--   Here $H_2$ denotes binary Shannon entropy in bits, with $0\log 0=0$.
-- source:
--   On the von Neumann capacity of noisy quantum channels, arXiv:quant-ph/9609024v3, PDF p. 9, III.D(ii), (3.42): quantum loss–fidelity Fano bound

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

/-- PDF pp.8–9, (3.42): two multiplies the ENTIRE bracket.
The L1 bound is the (3.37) consequence; dimension one is separated. -/
theorem loss_fidelity_fano
    [Nonempty R] [Nonempty A] [Nonempty B]
    (psi : EuclideanSpace ℂ (R × A)) (hpsi : IsState psi)
    (N : Superop A B) (M : Superop B A) (hN : IsChannel N) (hM : IsChannel M) :
    let rho := traceLeft (pureDensity psi)
    let F := referenceFidelity (M ∘ N) psi
    let d := Fintype.card R * Fintype.card A
    (2 ≤ d →
      loss (M ∘ N) rho ≤ 2 * (binEntropy2 F + (1 - F) * Real.logb 2 ((d : ℝ) - 1)) ∧
      loss N rho ≤ 2 * (binEntropy2 F + (1 - F) * Real.logb 2 ((d : ℝ) - 1))) ∧
    (d = 1 → F = 1 ∧ loss N rho = 0 ∧ loss (M ∘ N) rho = 0) := by sorry

end FiniteRegisters

end QAlgorithms.Papers.Independent.Gap48.P33
