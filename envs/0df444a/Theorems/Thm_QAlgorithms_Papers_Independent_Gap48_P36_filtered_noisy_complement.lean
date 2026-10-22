-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P36_filtered_noisy_complement
-- name    : QAlgorithms.Papers.Independent.Gap48.P36.filtered_noisy_complement
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:07:39.247823+00:00
-- url     : https://prove2.me/theorems/8da71525-208a-4a2c-83f2-ce45d26d1ad6
-- title:
--   Unnumbered formula (33): filtered canonical noisy complement
-- statement:
--   All Hilbert spaces have positive finite dimension. Channels are completely positive and trace preserving; conjugates use the same normalized pure-environment dilation. Let $T=(T_m)$ be a basis of $d^2$ unitaries on $\mathbb C^d$, including $I$, with $\operatorname{Tr}(T_m^\dagger T_n)=d\delta_{mn}$. Let $a_m\ge0$, $\sum_m a_m=1$, and $\Phi(\rho)=\sum_m a_mT_m\rho T_m^\dagger$. Write $N^{C,T}$ for the canonical conjugate using Kraus matrices $T_m/d$, and $\mathcal N^T=\{N^{C,T}(|\psi\rangle\langle\psi|):\|\psi\|=1\}$. With $A=\operatorname{diag}(a_m)$ and $\alpha_m=\sqrt{a_m}$, every input matrix obeys
--
--   $$
--   \Phi^{C,T}(\rho)=d^2\sqrt A\,N^{C,T}(\rho)\sqrt A=d^2\bigl(|\alpha\rangle\langle\alpha|\mathbin{*}N^{C,T}(\rho)\bigr).
--   $$
--
--   The filter is $d\sqrt A$. The correct displayed normalization is retained despite the scalar omission in the following prose.
-- source:
--   Properties of Conjugate Channels with Applications to Additivity and Multiplicativity, arXiv:quant-ph/0509126v3, PDF p. 14, Unnumbered formula (33): filtered canonical noisy complement

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

/-- Unnumbered formula (33), PDF p.14: all matrices; keep the d^2 factor.
Correction: the following prose prints filter sqrt(A); use d sqrt(A).
A filter contributes its scalar twice, giving the displayed d^2 in (33). -/
theorem filtered_noisy_complement [Nonempty A] [Nonempty K]
    (T : UnitaryBasis A K) (a : K → ℝ) (ha : ProbabilityWeights a) :
    ∀ rho : Matrix A A ℂ,
      randomComplement T.matrix a rho = (Fintype.card A : ℂ)^2 •
        (weightRoot a * noisyComplement T.matrix rho * weightRoot a) ∧
      randomComplement T.matrix a rho = (Fintype.card A : ℂ)^2 •
        Matrix.hadamard (fun j k => (Real.sqrt (a j) : ℂ) * (Real.sqrt (a k) : ℂ))
          (noisyComplement T.matrix rho) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P36

end
