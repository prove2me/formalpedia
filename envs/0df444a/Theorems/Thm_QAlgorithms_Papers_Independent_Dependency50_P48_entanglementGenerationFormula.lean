-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P48_entanglementGenerationFormula
-- name    : QAlgorithms.Papers.Independent.Dependency50.P48.entanglementGenerationFormula
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T15:42:32.500068+00:00
-- url     : https://prove2.me/theorems/4ab85e4b-d9c6-4481-805a-0e4a70bea692
-- title:
--   Entanglement-generation capacity equals regularized coherent information
-- statement:
--   Let $U:P\to Q\otimes E$ be an isometry on finite nonempty registers, and let $\mathcal N$ be its receiver channel. Define $E(\mathcal N)$ operationally: Alice prepares a unit vector on $A\otimes P^{\otimes n}$, with any positive integer $\dim A=\kappa$, and Bob applies a CPTP decoder to $Q^{\otimes n}$ with output dimension $\kappa$. The output has squared fidelity at least $1-\epsilon$ with $\kappa^{-1/2}\sum_{j=1}^{\kappa}|j,j\rangle$. No auxiliary communication or shared resource is supplied. Rates are $\log_2\kappa/n$, with every positive error and rate slack allowed for all sufficiently large $n$.
--
--   For $M_l=\max_{\rho}I_c(\rho,\mathcal N^{\otimes l})$, where $\rho$ ranges over all normalized density matrices on $P^{\otimes l}$, the maxima are attained and
--
--   $$E(\mathcal N)=\lim_{l\to\infty}\frac{M_l}{l}=\sup_{l\ge1}\frac{M_l}{l}.$$
--
--   Equivalently $M_l$ is the supremum of $H(B^l)_\sigma-H(RB^l)_\sigma$ over all unit pure vectors $\phi$ on $R\otimes P^{\otimes l}$, with $R$ isomorphic to $P^{\otimes l}$ and $\sigma=(\mathrm{id}_R\otimes\mathcal N^{\otimes l})(|\phi\rangle\langle\phi|)$. All entropies are in bits. This is an operational coding theorem for entanglement generation.
-- source:
--   The private classical capacity and quantum capacity of a quantum channel, arXiv:quant-ph/0304127v6, PDF p. 11, Theorem 5 / (36)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P48

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P48

open scoped BigOperators Matrix ComplexConjugate

open Filter

open QAlgorithms.Papers.Independent.Information100.P22 (coherentInformation)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

open QAlgorithms.Papers.Independent.Information100.P67 (dilationPower)

attribute [local instance] Classical.propDecidable

variable {P Q E X H : Type*}

variable [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]

variable [Fintype E] [DecidableEq E] [Fintype X] [DecidableEq X]

variable [Fintype H] [DecidableEq H]

/-- Theorem 5, (36), PDF p.11 (proof pp.11–14): operational unassisted
entanglement generation equals the coherent-information limit. The positive-block
supremum is the equivalent blocking form invoked after (6), p.4. -/
theorem entanglementGenerationFormula [Nonempty P] [Nonempty Q] [Nonempty E]
    (U : Matrix (Q × E) P ℂ) (hU : IsDilation U) :
    Tendsto (coherentRate U) atTop (nhds (generationCapacity U)) ∧
    generationCapacity U = regularizedCoherentInformation U ∧
    (∀ n : ℕ, 0 < n → ∃ rho : Matrix (Fin n → P) (Fin n → P) ℂ,
      IsDensityMatrix rho ∧
      coherentInformation (receiver (dilationPower U n)) rho = coherentMaximum (dilationPower U n)) ∧
    (∀ n : ℕ, 0 < n → coherentMaximum (dilationPower U n) =
      sSup {r | ∃ phi : EuclideanSpace ℂ ((Fin n → P) × (Fin n → P)), IsState phi ∧
        let sigma := idTensorSuperop (receiver (dilationPower U n)) (pureDensity phi)
        r = vnEntropy (traceLeft sigma) - vnEntropy sigma}) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P48

end
