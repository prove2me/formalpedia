-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P36_noisy_pure_conditions
-- name    : QAlgorithms.Papers.Independent.Gap48.P36.noisy_pure_conditions
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T04:58:35.678027+00:00
-- url     : https://prove2.me/theorems/faaebe5e-1415-4ff4-a925-33d01f7fe21e
-- title:
--   Theorem 12: projection, flat diagonal and stochastic modulus-square conditions
-- statement:
--   All Hilbert spaces have positive finite dimension. Channels are completely positive and trace preserving; conjugates use the same normalized pure-environment dilation. Let $T=(T_m)$ be a basis of $d^2$ unitaries on $\mathbb C^d$, including $I$, with $\operatorname{Tr}(T_m^\dagger T_n)=d\delta_{mn}$. Write $N^{C,T}$ for the canonical conjugate using Kraus matrices $T_m/d$, and $\mathcal N^T=\{N^{C,T}(|\psi\rangle\langle\psi|):\|\psi\|=1\}$. For a unit vector $\psi$ put $\gamma=N^{C,T}(|\psi\rangle\langle\psi|)$. Then
--
--   $$
--   \gamma^\dagger=\gamma,\quad(d\gamma)^2=d\gamma,\quad\operatorname{rank}(d\gamma)=d,\quad\gamma_{mm}=d^{-2}.
--   $$
--
--   If each $T_m^\dagger T_n$ is a scalar phase times some basis element, also $|\gamma_{mn}|\le d^{-2}$ and $D_{mn}=d^3|\gamma_{mn}|^2$ is nonnegative with all row and column sums one. These are necessary pure-image conditions.
-- source:
--   Properties of Conjugate Channels with Applications to Additivity and Multiplicativity, arXiv:quant-ph/0509126v3, PDF p. 19, Theorem 12: projection, flat diagonal and stochastic modulus-square conditions

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P36

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P36

open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder ENNReal

open QAlgorithms.Papers.Independent.Claimed50.P48

open QAlgorithms.Papers.Independent.Information100.P67 (receiverChannel complementaryChannel)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy normalizedChoi)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P03 (convexRoof)

open QAlgorithms.Papers.Independent.Dependency50.P45 (holevoCapacity)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C D E K L A2 B2 C2 : Type*}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]

variable [Fintype E] [DecidableEq E] [Fintype K] [DecidableEq K]

variable [Fintype L] [DecidableEq L] [Fintype A2] [DecidableEq A2]

variable [Fintype B2] [DecidableEq B2] [Fintype C2] [DecidableEq C2]

/-- Theorem 12, PDF pp.19–20: all four clauses, with only (c,d) requiring (35).
Correction to (c): replace the printed complex-entry order by modulus,
as required by the unitary expectation bound. The overbar in (d) is kept. -/
theorem noisy_pure_conditions [Nonempty A] [Nonempty K]
    (T : UnitaryBasis A K) (psi : EuclideanSpace ℂ A) (hpsi : IsState psi) :
    let gamma := noisyComplement T.matrix (pureDensity psi)
    gamma.IsHermitian ∧
    ((Fintype.card A : ℂ) • gamma) * ((Fintype.card A : ℂ) • gamma) =
        (Fintype.card A : ℂ) • gamma ∧
    Matrix.rank ((Fintype.card A : ℂ) • gamma) = Fintype.card A ∧
    (∀ k, gamma k k = ((Fintype.card A : ℂ)^2)⁻¹) ∧
    (PhaseClosed T → (∀ j k, ‖gamma j k‖ ≤ ((Fintype.card A : ℝ)^2)⁻¹) ∧
      DoublyStochastic (fun j k => (Fintype.card A : ℝ)^3 * Complex.normSq (gamma j k))) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P36

end
