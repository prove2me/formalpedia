-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P36_qubit_output_norm
-- name    : QAlgorithms.Papers.Independent.Gap48.P36.qubit_output_norm
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:11:55.251892+00:00
-- url     : https://prove2.me/theorems/f75629f2-6141-44fb-b87d-b74819c8846a
-- title:
--   Unnumbered appendix formula (93): exact unital-qubit output p-norm
-- statement:
--   All Hilbert spaces have positive finite dimension. Channels are completely positive and trace preserving; conjugates use the same normalized pure-environment dilation. Write $\nu_p(\Phi)=\sup_\rho\|\Phi(\rho)\|_p$ and $S_{\min}(\Phi)=\inf_\rho S(\Phi(\rho))$, with density inputs, Schatten norm, and von Neumann entropy. For a qubit Pauli probability channel with four nonnegative weights $a_k$ summing to one, label the identity by $0$ and the three axes by the nonzero binary Pauli labels. Put $\lambda_k=2(a_0+a_k)-1$ and choose $k_*$ maximizing $|\lambda_k|$. For real $p\ge1$,
--
--   $$
--   \nu_p(\Phi)=\left[\left(\frac{1+\lambda_{k_*}}2\right)^p+\left(\frac{1-\lambda_{k_*}}2\right)^p\right]^{1/p}=\left[(a_0+a_{k_*})^p+\left(\sum_{j\ne0,k_*}a_j\right)^p\right]^{1/p}.
--   $$
--
--   Both projectors $(I\pm\sigma_{k_*})/2$ are rank-one normalized optimizers with two nonzero Pauli coefficients, and they attain the sorted block bound. Here $\sigma_k$ is the Hermitian representative, using $iXZ=Y$ on the mixed label. Degenerate weights and $p=1$ are included.
-- source:
--   Properties of Conjugate Channels with Applications to Additivity and Multiplicativity, arXiv:quant-ph/0509126v3, PDF p. 31, Unnumbered appendix formula (93): exact unital-qubit output p-norm

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

/-- Unnumbered exact qubit formula (93), PDF p.31: largest absolute Bloch multiplier.
The two eigenvalues are (1 plus/minus lambda)/2, including lambda=0 and 1. -/
theorem qubit_output_norm (a : WeylLabel 2 → ℝ) (ha : ProbabilityWeights a)
    (k : WeylLabel 2) (hk : k ≠ 0)
    (hmax : ∀ j : WeylLabel 2, j ≠ 0 → |qubitLambda a j| ≤ |qubitLambda a k|)
    (p : ℝ) (hp : 1 ≤ p) :
    nu (ENNReal.ofReal p) (randomUnitary (finWeyl 2) a) =
      Real.rpow (Real.rpow ((1 + qubitLambda a k) / 2) p +
        Real.rpow ((1 - qubitLambda a k) / 2) p) (1 / p) ∧
    nu (ENNReal.ofReal p) (randomUnitary (finWeyl 2) a) =
      Real.rpow (Real.rpow (a 0 + a k) p +
        Real.rpow (∑ j ∈ (Finset.univ.erase 0).erase k, a j) p) (1 / p) ∧
    (∀ positive : Bool, IsDensityMatrix (qubitAxisState k positive) ∧
      Matrix.rank (qubitAxisState k positive) = 1 ∧
      FlatSupport (finWeyl 2) (qubitAxisState k positive) 2 ∧
      schattenNorm (ENNReal.ofReal p) (randomUnitary (finWeyl 2) a (qubitAxisState k positive)) =
        nu (ENNReal.ofReal p) (randomUnitary (finWeyl 2) a)) ∧
    (∀ e : (Fin 2 × Fin 2) ≃ WeylLabel 2, SortedRows a e →
      nu (ENNReal.ofReal p) (randomUnitary (finWeyl 2) a) = blockBound p a e) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P36

end
