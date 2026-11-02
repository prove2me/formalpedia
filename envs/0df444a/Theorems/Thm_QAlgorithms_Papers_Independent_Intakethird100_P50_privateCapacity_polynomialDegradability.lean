-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P50_privateCapacity_polynomialDegradability
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P50.privateCapacity_polynomialDegradability
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:55:26.019051+00:00
-- url     : https://prove2.me/theorems/2eea08df-c9c9-4184-87fb-d7de91664c40
-- title:
--   Lemma 10: quantitative private-capacity expansion from polynomial degradability
-- statement:
--   All systems are nonzero finite-dimensional complex Hilbert spaces. A channel is complex-linear, completely positive and trace preserving. Its receiver and full complementary channel are obtained from the same isometric dilation. Write $Q(N)$ and $P(N)$ for the unassisted operational quantum and private capacities, allowing arbitrary collective codes over independent uses with vanishing reliability error and environmental leakage. Write $I_c(N)=\max_\rho[S(N(\rho))-S(N^c(\rho))]$, where the maximum includes every density operator. Entropies and logarithms are in bits, with $0\log 0=0$. The diamond norm has no factor $1/2$.
--
--   Let $N(p):A\to B$ be channels for $p\in[0,1]$ with fixed finite input/output spaces and a common finite dilation space. Let $r>1$ and $c\ge0$, and suppose $\operatorname{dg}(N(p))\le cp^r$ throughout this interval. Here $\operatorname{dg}$ is the minimum, over all CPTP maps $D:B\to E$, of $\|N^c-D\circ N\|_\diamond$. If $c=0$, then $P(N(p))=I_c(N(p))$ for every physical $p$. If $c>0$, there are $K\ge0$ and $0<\delta\le1$ such that, for every $0<p<\delta$, writing $e(p)$ for the actual Choi rank, rank-one values have exact equality and rank $e(p)\ge2$ satisfies
--   $$
--   |P(N(p))-I_c(N(p))|\le L_P(e(p),c,r,p)+Kp^{2r},
--   \qquad L_P(e,c,r,p)=3crp^{r-1}(-p\log_2p)+cp^r\left[-3\log_2c+3+\frac3{\ln2}+\log_2(e-1)+4\log_2e\right].
--   $$
--   The Choi rank may vary with $p$; no constant-rank assumption is required. This gives the quantitative capacity expansion from polynomial approximate degradability.
-- source:
--   Quantum and private capacities of low-noise channels, arXiv:1705.04335v3, PDF p. 10, Lemma 10: quantitative private-capacity expansion from polynomial degradability

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

/-- Lemma 10, PDF p.10: private-capacity analogue, with O(p^(2r)) remainder.
There is no constant-rank or positive-c exclusion of exact-degradable boundaries. -/
theorem privateCapacity_polynomialDegradability [Nonempty A] [Nonempty B] [Nonempty E]
    (V : ℝ → Matrix (B × E) A ℂ)
    (hV : ∀ p ∈ Set.Icc 0 1, IsIsometry (V p))
    (c r : ℝ) (hc : 0 ≤ c) (hr : 1 < r)
    (hdg : ∀ p ∈ Set.Icc 0 1, degradability (V p) ≤ c * p ^ r) :
    (c = 0 → ∀ p ∈ Set.Icc 0 1, fullTracePrivateCapacity (V p) = maximumCoherentInformation (V p)) ∧
    (0 < c → ∃ K : ℝ, 0 ≤ K ∧ ∃ delta : ℝ, 0 < delta ∧ delta ≤ 1 ∧
      ∀ p ∈ Set.Ioo 0 delta,
        if dilationChoiRank (V p) = 1 then fullTracePrivateCapacity (V p) = maximumCoherentInformation (V p)
        else |fullTracePrivateCapacity (V p) - maximumCoherentInformation (V p)| ≤
          privatePolynomialLeading (dilationChoiRank (V p)) c r p + K * p ^ (2 * r)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P50

end
