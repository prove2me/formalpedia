-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P50_quantumCapacity_polynomialDegradability
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P50.quantumCapacity_polynomialDegradability
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:54:32.872134+00:00
-- url     : https://prove2.me/theorems/f8494f0c-fa12-4d0b-9aa7-bf8d3124f589
-- title:
--   Lemma 9: quantitative quantum-capacity expansion from polynomial degradability
-- statement:
--   All systems are nonzero finite-dimensional complex Hilbert spaces. A channel is complex-linear, completely positive and trace preserving. Its receiver and full complementary channel are obtained from the same isometric dilation. Write $Q(N)$ and $P(N)$ for the unassisted operational quantum and private capacities, allowing arbitrary collective codes over independent uses with vanishing reliability error and environmental leakage. Write $I_c(N)=\max_\rho[S(N(\rho))-S(N^c(\rho))]$, where the maximum includes every density operator. Entropies and logarithms are in bits, with $0\log 0=0$. The diamond norm has no factor $1/2$.
--
--   Let $N(p):A\to B$ be channels for $p\in[0,1]$ with fixed finite input/output spaces and a common finite dilation space. Let $r>1$ and $c\ge0$, and suppose $\operatorname{dg}(N(p))\le cp^r$ throughout this interval. Here $\operatorname{dg}$ is the minimum, over all CPTP maps $D:B\to E$, of $\|N^c-D\circ N\|_\diamond$. If $c=0$, then $Q(N(p))=I_c(N(p))$ for every physical $p$. If $c>0$, there are $K\ge0$ and $0<\delta\le1$ such that, for every $0<p<\delta$, writing $e(p)$ for the actual Choi rank, rank-one values have exact equality and rank $e(p)\ge2$ satisfies
--   $$
--   |Q(N(p))-I_c(N(p))|\le L_Q(e(p),c,r,p)+Kp^{3r},
--   \qquad L_Q(e,c,r,p)=crp^{r-1}(-p\log_2p)+cp^r\left[-\log_2c+1+\frac1{\ln2}+\log_2e+\frac12\log_2(e-1)\right].
--   $$
--   The Choi rank may vary with $p$; no constant-rank assumption is required. This gives the quantitative capacity expansion from polynomial approximate degradability.
-- source:
--   Quantum and private capacities of low-noise channels, arXiv:1705.04335v3, PDF p. 9, Lemma 9: quantitative quantum-capacity expansion from polynomial degradability

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

/-- Lemma 9, PDF p.9: actual Choi rank may vary. The c=0 and rank-one cases are
exact, and the general branch retains the O(p^(3r)) remainder. -/
theorem quantumCapacity_polynomialDegradability [Nonempty A] [Nonempty B] [Nonempty E]
    (V : ℝ → Matrix (B × E) A ℂ)
    (hV : ∀ p ∈ Set.Icc 0 1, IsIsometry (V p))
    (c r : ℝ) (hc : 0 ≤ c) (hr : 1 < r)
    (hdg : ∀ p ∈ Set.Icc 0 1, degradability (V p) ≤ c * p ^ r) :
    (c = 0 → ∀ p ∈ Set.Icc 0 1, dilationQuantumCapacity (V p) = maximumCoherentInformation (V p)) ∧
    (0 < c → ∃ K : ℝ, 0 ≤ K ∧ ∃ delta : ℝ, 0 < delta ∧ delta ≤ 1 ∧
      ∀ p ∈ Set.Ioo 0 delta,
        if dilationChoiRank (V p) = 1 then dilationQuantumCapacity (V p) = maximumCoherentInformation (V p)
        else |dilationQuantumCapacity (V p) - maximumCoherentInformation (V p)| ≤
          quantumPolynomialLeading (dilationChoiRank (V p)) c r p + K * p ^ (3 * r)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P50

end
