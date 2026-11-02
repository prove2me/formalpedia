-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P50_polynomialPauli_modifiedComplement
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P50.polynomialPauli_modifiedComplement
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:00:51.408208+00:00
-- url     : https://prove2.me/theorems/6a0ee3f4-ec0a-4b34-a719-2dc58dd62ea7
-- title:
--   Theorem 15: polynomial Pauli channels and a modified-complement degrader
-- statement:
--   Let $p_1,p_2,p_3$ be real polynomials with $p_i(0)=0$. Put $p_0(t)=1-\sum_{i=1}^3p_i(t)$, and assume these four weights form a probability distribution for every $t$ in a right neighborhood of zero. Let $c_i$ be the coefficient of $t$ in $p_i$, set $C=|c_1c_2+c_1c_3+c_2c_3|$, and let $N_t$ be the associated qubit Pauli channel with canonical Kraus-label complement. For every fixed choice of real $a_1,a_2,a_3$ satisfying $a_i=4\sum_{j\ne i}c_j$ whenever $c_i\ne0$, define $q_i(t)=p_i(t+a_it^2)$ for $i=1,2,3$ and $q_0(t)=1-\sum_iq_i(t)$. The $q_i(t)$ are physical eventually, and
--   $$
--   \|N_t^c-N_{q(t)}^c\circ N_t\|_\diamond=O(t^2).
--   $$
--   Independently, there are $K\ge0$ and $0<\delta\le1$ such that
--   $$
--   \operatorname{dg}(N_t)\le256C t^2+Kt^3\qquad(0<t<\delta).
--   $$
--   The constants may depend on the fixed polynomial family (and on the fixed $a_i$ for the first bound), but not on $t$. When $c_i=0$, $a_i$ is unrestricted, and the scalar bound includes $C=0$. This retains both numbered conclusions (23) and (24).
-- source:
--   Quantum and private capacities of low-noise channels, arXiv:1705.04335v3, PDF p. 16, Theorem 15: polynomial Pauli channels and a modified-complement degrader

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P50

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Intakethird100.P50

variable {A B E F : Type}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype E] [DecidableEq E] [Fintype F] [DecidableEq F]

open QAlgorithms.Papers.Independent.Information100.P67
  (IsIsometry receiverChannel complementaryChannel maximumCoherentInformation
    dilationPower idealJoint)

open QAlgorithms.Papers.Independent.Information100.P80 (log2)

open QAlgorithms.Papers.Independent.Information100.P69 (diamond choi)

open QAlgorithms.Papers.Independent.Support50.P07 (fullTracePrivateCapacity)

open QAlgorithms.Papers.Independent.Frontier18.P17 (clock)

/-- Theorem 15, PDF pp.16,20–21: polynomial evaluation in (22), arbitrary a_i
when c_i=0, and the sharp scalar bound (24) even when its coefficient is zero.
Source proof audit: the intermediate O(p^(5/2)) assertion at c_i=0 is not used
as a hypothesis or stated as a result; see MODERATION_NOTES.md. -/
theorem polynomialPauli_modifiedComplement (P : Fin 3 → Polynomial ℝ)
    (hP : PolynomialNoise P) :
    (∀ a : Fin 3 → ℝ,
      (∀ i, linearCoefficient P i ≠ 0 →
        a i = 4 * ∑ j ∈ Finset.univ.erase i, linearCoefficient P j) →
      ∃ K : ℝ, 0 ≤ K ∧ ∃ delta : ℝ, 0 < delta ∧ delta ≤ 1 ∧
        ∀ p ∈ Set.Ioo 0 delta,
          Probabilities (modifiedWeights P a p) ∧
          diamond (channelDifference (complementaryChannel (pauliDilation (polynomialWeights P p)))
            (complementaryChannel (pauliDilation (modifiedWeights P a p)) ∘
              receiverChannel (pauliDilation (polynomialWeights P p)))) ≤ K * p ^ 2) ∧
    (∃ K : ℝ, 0 ≤ K ∧ ∃ delta : ℝ, 0 < delta ∧ delta ≤ 1 ∧
      ∀ p ∈ Set.Ioo 0 delta,
        degradability (pauliDilation (polynomialWeights P p)) ≤
          256 * pairCoefficient P * p ^ 2 + K * p ^ 3) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P50

end
