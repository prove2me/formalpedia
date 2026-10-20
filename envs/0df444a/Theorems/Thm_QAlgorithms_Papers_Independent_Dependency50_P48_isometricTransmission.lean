-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P48_isometricTransmission
-- name    : QAlgorithms.Papers.Independent.Dependency50.P48.isometricTransmission
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T15:45:54.042445+00:00
-- url     : https://prove2.me/theorems/81ad8f17-b351-4fc7-a9ef-b145d4c35ae8
-- title:
--   Isometric transmission codes from the pure-alphabet construction
-- statement:
--   Fix a normalized input density matrix $\rho$ and a finite-dimensional channel $\mathcal N$ given by an isometry $P\to Q\otimes E$ on nonempty registers. All entropies are in bits. For every $\epsilon,\delta>0$ and every sufficiently large positive $n$, there are a positive integer $\kappa$, an isometry $V:\mathbb C^{\kappa}\to P^{\otimes n}$, and a CPTP decoder $D:Q^{\otimes n}\to\mathbb C^{\kappa}$ such that
--
--   $$\frac{\log_2\kappa}{n}\ge I_c(\rho,\mathcal N)-\delta.$$
--
--   The same encoder and decoder have squared fidelity at least $1-\epsilon$ for every state $|\Psi_\alpha\rangle=\sum_j\alpha_j|j,j\rangle$ with $\sum_j|\alpha_j|^2=1$ in the displayed fixed Schmidt basis:
--
--   $$F\!\left(|\Psi_\alpha\rangle,(\mathrm{id}\otimes D\circ\mathcal N^{\otimes n}\circ[V(\cdot)V^\dagger])(|\Psi_\alpha\rangle\langle\Psi_\alpha|)\right)\ge1-\epsilon.$$
--
--   The reference is untouched, and there is no initial shared resource or auxiliary channel. This existence result comes from the orthogonal pure-alphabet codewords; it does not restrict arbitrary encoders in a converse.
-- source:
--   The private classical capacity and quantum capacity of a quantum channel, arXiv:quant-ph/0304127v6, PDF p. 18, Appendix D / (58)–(59)

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

/-- Appendix D, (58)–(59), PDF p.18: pure-alphabet codes give isometric
transmission at rate at least Ic(rho,N)-delta. The same code works for all
Schmidt coefficient lists in the displayed basis, with untouched reference.
This does not assert that arbitrary encoders are isometric. -/
theorem isometricTransmission [Nonempty P] [Nonempty Q] [Nonempty E]
    (U : Matrix (Q × E) P ℂ) (hU : IsDilation U)
    (rho : Matrix P P ℂ) (hrho : IsDensityMatrix rho) :
    ∀ eps > (0 : ℝ), ∀ delta > (0 : ℝ), ∃ n0 : ℕ, 0 < n0 ∧ ∀ n ≥ n0,
      ∃ k : ℕ, 0 < k ∧ ∃ C : IsometricCode (Fin n → P) (Fin n → Q) k,
        coherentInformation (receiver U) rho - delta ≤ Real.logb 2 (k : ℝ) / (n : ℝ) ∧
        ∀ alpha : Fin k → ℂ, (∑ j, Complex.normSq (alpha j)) = 1 →
          1 - eps ≤ pureFidelity (diagonalSchmidtVector alpha)
            (idTensorSuperop (C.logicalMap (receiver (dilationPower U n)))
              (pureDensity (diagonalSchmidtVector alpha))) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P48

end
