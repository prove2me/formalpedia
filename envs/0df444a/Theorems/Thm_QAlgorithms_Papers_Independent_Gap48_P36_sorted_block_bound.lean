-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P36_sorted_block_bound
-- name    : QAlgorithms.Papers.Independent.Gap48.P36.sorted_block_bound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:00:09.201244+00:00
-- url     : https://prove2.me/theorems/611bf9a0-303f-4318-a7ca-0dbc73361408
-- title:
--   Theorem 15: sorted block-sum bound (inequality clause)
-- statement:
--   All Hilbert spaces have positive finite dimension. Channels are completely positive and trace preserving; conjugates use the same normalized pure-environment dilation. Let $T=(T_m)$ be a basis of $d^2$ unitaries on $\mathbb C^d$, including $I$, with $\operatorname{Tr}(T_m^\dagger T_n)=d\delta_{mn}$. Let $a_m\ge0$, $\sum_m a_m=1$, and $\Phi(\rho)=\sum_m a_mT_m\rho T_m^\dagger$. Write $\nu_p(\Phi)=\sup_\rho\|\Phi(\rho)\|_p$ and $S_{\min}(\Phi)=\inf_\rho S(\Phi(\rho))$, with density inputs, Schatten norm, and von Neumann entropy. Reorder all labeled weights by a permutation as $b_0\ge\cdots\ge b_{d^2-1}$ and define $\beta_j=\sum_{i=0}^{d-1}b_{i+jd}$. For each real $p\ge1$,
--
--   $$
--   \nu_p(\Phi)=\nu_p(\Phi^{C,T})\le\left(\sum_{j=0}^{d-1}\beta_j^p\right)^{1/p}.
--   $$
--
--   The additional equality/decomposability assertion is inventoried separately as deferred. Ties never merge distinct labels.
-- source:
--   Properties of Conjugate Channels with Applications to Additivity and Multiplicativity, arXiv:quant-ph/0509126v3, PDF p. 22, Theorem 15: sorted block-sum bound (inequality clause)

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

/-- Theorem 15 inequality clause, PDF pp.22–24: a permutation preserves tied labels.
Its additional equality/decomposability clause is separately deferred. -/
theorem sorted_block_bound (d : ℕ) [NeZero d]
    (T : UnitaryBasis (Fin d) K) (a : K → ℝ) (ha : ProbabilityWeights a)
    (e : (Fin d × Fin d) ≃ K) (hs : SortedRows a e) (p : ℝ) (hp : 1 ≤ p) :
    nu (ENNReal.ofReal p) (randomUnitary T.matrix a) =
      nu (ENNReal.ofReal p) (randomComplement T.matrix a) ∧
    nu (ENNReal.ofReal p) (randomUnitary T.matrix a) ≤ blockBound p a e := by sorry

end QAlgorithms.Papers.Independent.Gap48.P36

end
