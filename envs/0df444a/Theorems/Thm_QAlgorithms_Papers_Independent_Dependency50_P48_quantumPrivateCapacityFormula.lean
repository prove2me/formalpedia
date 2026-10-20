-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P48_quantumPrivateCapacityFormula
-- name    : QAlgorithms.Papers.Independent.Dependency50.P48.quantumPrivateCapacityFormula
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T15:39:50.244919+00:00
-- url     : https://prove2.me/theorems/331873d0-90b6-4a61-94f1-708ae93b248b
-- title:
--   Quantum private/key capacity as regularized private information
-- statement:
--   Let $U:P\to Q\otimes E$ be an isometry between finite nonempty registers, defining $\mathcal N(\rho)=\operatorname{Tr}_E(U\rho U^\dagger)$ and its full complementary output $\mathcal N^c(\rho)$. For every normalized density matrix $\rho$, define coherent and private information, in bits, by
--
--   $$I_c(\rho,\mathcal N)=H(\mathcal N(\rho))-H(\mathcal N^c(\rho)),$$
--   $$I_p(\rho,\mathcal N)=I_c(\rho,\mathcal N)-\min_{\sum_xp_x\rho_x=\rho}\sum_xp_xI_c(\rho_x,\mathcal N).$$
--
--   The minimum ranges over all finite probability ensembles of normalized, possibly mixed, input states. For each positive blocklength both this decomposition minimum and the maximum over $\rho$ are attained. The operational private-message and secret-key capacities, with separate error and leakage constraints and allowing forward public communication, satisfy
--
--   $$C_p(\mathcal N)=K(\mathcal N)=\lim_{l\to\infty}\frac1l\max_{\rho\text{ on }P^{\otimes l}}I_p(\rho,\mathcal N^{\otimes l}).$$
--
--   There is no initial shared key, entanglement, or backward channel. Inputs may be mixed and entangled across uses. This formula preserves the distinction between private and coherent information.
-- source:
--   The private classical capacity and quantum capacity of a quantum channel, arXiv:quant-ph/0304127v6, PDF p. 9, Equations (30)–(31)

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

/-- Equation (30), PDF p.9: quantum private/key capacity equals regularized
private information. The rho maximum and the decomposition minimum in (31)
are attained. All input and component states may be mixed. -/
theorem quantumPrivateCapacityFormula [Nonempty P] [Nonempty Q] [Nonempty E]
    (U : Matrix (Q × E) P ℂ) (hU : IsDilation U) :
    quantumPrivateCapacity U .message true = quantumPrivateCapacity U .key true ∧
    Tendsto (privateRate U) atTop (nhds (quantumPrivateCapacity U .message true)) ∧
    (∀ n : ℕ, 0 < n → ∃ rho : Matrix (Fin n → P) (Fin n → P) ℂ,
      IsDensityMatrix rho ∧
      privateInformation (dilationPower U n) rho = privateMaximum (dilationPower U n)) ∧
    (∀ n : ℕ, 0 < n → ∀ rho : Matrix (Fin n → P) (Fin n → P) ℂ,
      IsDensityMatrix rho → ∃ D : Decomposition (Fin n → P), D.average = rho ∧
        (∑ j, D.probability j * coherentInformation (receiver (dilationPower U n)) (D.state j)) =
          sInf (coherentDecompositionCosts (dilationPower U n) rho)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P48

end
