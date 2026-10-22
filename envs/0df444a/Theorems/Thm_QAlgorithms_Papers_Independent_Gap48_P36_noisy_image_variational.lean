-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P36_noisy_image_variational
-- name    : QAlgorithms.Papers.Independent.Gap48.P36.noisy_image_variational
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T04:56:28.01+00:00
-- url     : https://prove2.me/theorems/e72bbd2d-e705-4c92-a828-645dc4324e9f
-- title:
--   Theorem 8: variational formula over the noisy-conjugate pure image
-- statement:
--   All Hilbert spaces have positive finite dimension. Channels are completely positive and trace preserving; conjugates use the same normalized pure-environment dilation. Let $T=(T_m)$ be a basis of $d^2$ unitaries on $\mathbb C^d$, including $I$, with $\operatorname{Tr}(T_m^\dagger T_n)=d\delta_{mn}$. Let $a_m\ge0$, $\sum_m a_m=1$, and $\Phi(\rho)=\sum_m a_mT_m\rho T_m^\dagger$. Write $N^{C,T}$ for the canonical conjugate using Kraus matrices $T_m/d$, and $\mathcal N^T=\{N^{C,T}(|\psi\rangle\langle\psi|):\|\psi\|=1\}$. Write $\nu_p(\Phi)=\sup_\rho\|\Phi(\rho)\|_p$ and $S_{\min}(\Phi)=\inf_\rho S(\Phi(\rho))$, with density inputs, Schatten norm, and von Neumann entropy. Put $A=\operatorname{diag}(a_m)$. For real $p\ge1$,
--
--   $$
--   \nu_p(\Phi)=d^2\sup_{\gamma\in\mathcal N^T}\|\sqrt A\gamma\sqrt A\|_p=d^3\sup_{\gamma\in\mathcal N^T}\|\gamma A\gamma\|_p.
--   $$
--
--   This is the variational formulation over the fixed noisy-conjugate pure image.
-- source:
--   Properties of Conjugate Channels with Applications to Additivity and Multiplicativity, arXiv:quant-ph/0509126v3, PDF p. 14, Theorem 8: variational formula over the noisy-conjugate pure image

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

/-- Theorem 8, PDF p.14, (34): the second factor is d^3, not d^2. -/
theorem noisy_image_variational [Nonempty A] [Nonempty K]
    (T : UnitaryBasis A K) (a : K → ℝ) (ha : ProbabilityWeights a) (p : ℝ) (hp : 1 ≤ p) :
    nu (ENNReal.ofReal p) (randomUnitary T.matrix a) =
      (Fintype.card A : ℝ)^2 * sSup {x | ∃ gamma ∈ pureNoisyImage T.matrix,
        x = schattenNorm (ENNReal.ofReal p) (weightRoot a * gamma * weightRoot a)} ∧
    nu (ENNReal.ofReal p) (randomUnitary T.matrix a) =
      (Fintype.card A : ℝ)^3 * sSup {x | ∃ gamma ∈ pureNoisyImage T.matrix,
        x = schattenNorm (ENNReal.ofReal p) (gamma * weightMatrix a * gamma)} := by sorry

end QAlgorithms.Papers.Independent.Gap48.P36

end
