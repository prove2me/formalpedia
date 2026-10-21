-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P36_typicalSequenceRandomCodes
-- name    : QAlgorithms.Papers.Independent.Renew46.P36.typicalSequenceRandomCodes
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T22:08:39.180596+00:00
-- url     : https://prove2.me/theorems/41243160-116c-4c0e-b58b-e96c8b3081c5
-- title:
--   Proposition 5: typical-sequence random quantum codes
-- statement:
--   Fix a CPTP channel $\mathcal N:A'\to B$ between finite nonzero registers and a finite ensemble $\mathcal E=\{p_x,\rho_x\}$ of density operators on $A'$, with $p_x\geq0$ and $\sum_xp_x=1$. Entropies and rates are in bits, and $I_c(\rho_x,\mathcal N)$ is output entropy minus reference–output entropy after sending half of a normalized purification. A word $x^n$ is $\delta$-typical when $|N(x\mid x^n)-np_x|\leq n\delta$ for every letter, including zero-probability letters.
--
--   There is a constant $c>0$, depending only on the fixed channel and ensemble, such that for all $\epsilon,\delta>0$, every sufficiently large positive $n$, and every such typical word, there is a finite random quantum code with common positive integer logical dimension $k$ satisfying
--
--   $$
--   \frac{\log_2k}{n}\geq\sum_xp_x I_c(\rho_x,\mathcal N)-c\delta,\qquad
--   \left\|\sum_\alpha P_\alpha\mathcal E_\alpha(I_k/k)-\bigotimes_{i=1}^{n}\rho_{x_i}\right\|_1\leq\epsilon.
--   $$
--
--   Here $P_\alpha$ is a probability distribution over CPTP encoder–decoder pairs. Every realization transmits half of the normalized $k$-dimensional maximally entangled state through $\mathcal N^{\otimes n}$ with squared fidelity at least $1-\epsilon$. The constant precedes the tolerances, block length, and typical word; the block threshold is uniform over words.
--
--   This is the ensemble-type random-coding extension used by the simultaneous coding theorem. The source's exact-rate notation is interpreted by the lower bound established in its proof, allowing integer rounding and negative lower bounds without negative code dimensions.
-- source:
--   The capacity of a quantum channel for simultaneous transmission of classical and quantum information, arXiv:quant-ph/0311131v3, PDF p. 8, Proposition 5: typical-sequence random quantum codes

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P36

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Renew46.P36

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P08 (Ensemble canonicalPurification)

open QAlgorithms.Papers.Independent.Dependency50.P07 (Typical)

open QAlgorithms.Papers.Independent.Information100.P27 (qubitDephasing)

open QAlgorithms.Papers.Independent.Dependency50.P41 (maximallyEntangled)

open QAlgorithms.Papers.Independent.Claimed50.P20 (DynamicPureEnsemble pureOutputs cqHolevoBits conditionalCoherent)

open QAlgorithms.Papers.Independent.Information100.P67
  (IsDegradable receiverChannel complementaryChannel maximumCoherentInformation squaredFidelity)

open QAlgorithms.Papers.Independent.Information100.P76 (maximallyMixed)

open QAlgorithms.Papers.Independent.Information100.P80 (quantumCapacity)

open QAlgorithms.Papers.Independent.Next46.P40
  (dephasingIsometry generalizedDephasing diagonalPart)

variable {A B E A1 A2 E1 E2 : Type}

variable [Fintype A] [Fintype B] [Fintype E]

variable [Fintype A1] [Fintype A2] [Fintype E1] [Fintype E2]

/-- Proposition 5, PDF pp.7--9. One constant precedes epsilon, delta, n, and EVERY
typical word; it may depend on the fixed ensemble/channel. The p.8 proof gives a
rate LOWER bound, interpreted with integer rounding; rates need not be negative
when the lower bound is negative. Typicality is inclusive and allows zero weights. -/
theorem typicalSequenceRandomCodes
    [Nonempty A] [Nonempty B] (N : Superop A B) (hN : IsChannel N) (P : Ensemble A) :
    ∃ c : ℝ, 0 < c ∧ ∀ epsilon : ℝ, 0 < epsilon → ∀ delta : ℝ, 0 < delta →
      ∃ n0 : ℕ, 0 < n0 ∧ ∀ n ≥ n0, ∀ word : Fin n → Fin P.size,
        Typical P.prob n delta word → ∃ C : RandomQuantumCode A B n,
          C.GoodType N P word epsilon ∧
          (∑ x, P.prob x * inputCoherentInformation N (P.state x)) - c * delta ≤
            Real.logb 2 (C.logical : ℝ) / (n : ℝ) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P36

end
