-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P36_pauli_two_norm
-- name    : QAlgorithms.Papers.Independent.Gap48.P36.pauli_two_norm
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T04:57:09.672476+00:00
-- url     : https://prove2.me/theorems/58a3adec-a9e3-4a40-a70f-77ffef7280aa
-- title:
--   Proposition 9: Pauli-diagonal 2-norm bound and qutrit attainment
-- statement:
--   All Hilbert spaces have positive finite dimension. Channels are completely positive and trace preserving; conjugates use the same normalized pure-environment dilation. Use $X|k\rangle=|k+1\bmod d\rangle$, $Z|k\rangle=e^{2\pi ik/d}|k\rangle$, $W_{jk}=X^jZ^k$, and labels $(j,k)\in(\mathbb Z/d\mathbb Z)^2$. Write $\nu_p(\Phi)=\sup_\rho\|\Phi(\rho)\|_p$ and $S_{\min}(\Phi)=\inf_\rho S(\Phi(\rho))$, with density inputs, Schatten norm, and von Neumann entropy. Let $d\ge2$ and $\Phi(\rho)=\sum_{m,n}a_{mn}W_{mn}\rho W_{mn}^\dagger$ with nonnegative weights summing to one. Define $\lambda_{jk}=e^{2\pi ijk/d}\sum_{m,n}a_{mn}e^{2\pi i(mk-jn)/d}$, used only through its modulus, and $M=\max_{(j,k)\ne0}|\lambda_{jk}|^2$. Then
--
--   $$
--   \nu_2(\Phi)\le\sqrt{\frac{1+(d-1)M}{d}}.
--   $$
--
--   For $d=3$, each maximizing nonzero label gives a rank-one density $(I+W+W^2)/3$, $W=X^{j_*}Z^{k_*}$, attaining the bound and maximum. No phase-sensitive eigenvalue claim from (38)–(40) is made.
-- source:
--   Properties of Conjugate Channels with Applications to Additivity and Multiplicativity, arXiv:quant-ph/0509126v3, PDF p. 16, Proposition 9: Pauli-diagonal 2-norm bound and qutrit attainment

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

/-- Proposition 9, PDF pp.16–17: use (39) only in modulus, as in (42).
Correction: the Fourier exponent printed i2pi i/d is read as 2pi i/d;
unitary conjugation (36)-(37) and (43) require a phase, not a real exponential.
The remaining extraneous phase is retained and disappears in modulus.
At d=3 the WHOLE bracket is divided by three. -/
theorem pauli_two_norm (d : ℕ) [NeZero d] (hd : 2 ≤ d) (a : WeylLabel d → ℝ) (ha : ProbabilityWeights a) :
    nu 2 (randomUnitary (finWeyl d) a) ≤ pauliTwoBound d a ∧
    (d = 3 → ∀ jk : WeylLabel d, jk ≠ 0 →
      ‖printedMultiplier d a jk‖^2 = maxPauliMultiplierSq d a →
      let rho := (3 : ℂ)⁻¹ • (1 + finWeyl d jk + finWeyl d jk ^ 2)
      IsDensityMatrix rho ∧ Matrix.rank rho = 1 ∧ schattenNorm 2 (randomUnitary (finWeyl d) a rho) =
        nu 2 (randomUnitary (finWeyl d) a) ∧ nu 2 (randomUnitary (finWeyl d) a) = pauliTwoBound d a) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P36

end
