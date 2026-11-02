-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P50_approximatelyRecoverable_capacities
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P50.approximatelyRecoverable_capacities
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:04:10.002191+00:00
-- url     : https://prove2.me/theorems/93ea44ff-6baf-4e70-87e4-10f99f3978db
-- title:
--   §5 unnumbered extension: approximately recoverable channels
-- statement:
--   All systems are nonzero finite-dimensional complex Hilbert spaces. A channel is complex-linear, completely positive and trace preserving. Its receiver and full complementary channel are obtained from the same isometric dilation. Write $Q(N)$ and $P(N)$ for the unassisted operational quantum and private capacities, allowing arbitrary collective codes over independent uses with vanishing reliability error and environmental leakage. Write $I_c(N)=\max_\rho[S(N(\rho))-S(N^c(\rho))]$, where the maximum includes every density operator. Entropies and logarithms are in bits, with $0\log 0=0$. The diamond norm has no factor $1/2$.
--
--   Fix input and receiver spaces $A,B$. Let $N:A\to B$ and $M:B\to A$ be channels. Choose compatible dilations $V:A\to B\otimes E_1$ and $W:B\to A\otimes E_2$ and the sequential dilation of $M\circ N$, with environment ordered $E_1\otimes E_2$. On every input operator $X$,
--   $$
--   \operatorname{Tr}_{E_2}(M\circ N)^c(X)=N^c(X).
--   $$
--   Define the CPTP degrader $D=\operatorname{Tr}_{E_2}\circ(M\circ N)^c\circ M$. For any $0\le\varepsilon\le2$ satisfying $\|M\circ N-\mathrm{id}_A\|_\diamond\le\varepsilon$,
--   $$
--   \|N^c-D\circ N\|_\diamond\le2\varepsilon^{3/2}.
--   $$
--   Moreover, there are $C_Q,C_P\ge0$ and $0<\delta\le2$, uniform over these channels and their dilations at fixed $A,B$, such that for $0\le\varepsilon\le\delta$ the original channel $N$ satisfies exactly the two capacity bounds below, with its own actual Choi rank $e$. If $e=1$ or $\varepsilon=0$, $Q(N)=P(N)=I_c(N)$; otherwise:
--   $$
--   |Q(N)-I_c(N)|\le-3\varepsilon^{3/2}\log_2\varepsilon+2\varepsilon^{3/2}\left[\frac1{\ln2}+\log_2e+\tfrac12\log_2(e-1)\right]+C_Q\varepsilon^{9/2},
--   $$
--   $$
--   |P(N)-I_c(N)|\le-9\varepsilon^{3/2}\log_2\varepsilon+2\varepsilon^{3/2}\left[\frac3{\ln2}+4\log_2e+\log_2(e-1)\right]+C_P\varepsilon^3.
--   $$
--   This extends the low-noise conclusion to approximately recoverable channels even when their input and receiver dimensions differ.
-- source:
--   Quantum and private capacities of low-noise channels, arXiv:1705.04335v3, PDF p. 18, §5 unnumbered extension: approximately recoverable channels

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

/-- §5 unnumbered extension, PDF pp.18–19: compatible dilations give the partial
trace identity on ALL matrices and the specified degrader for the ORIGINAL N.
The full norm inequality and all Theorem 12 remainders are retained. -/
theorem approximatelyRecoverable_capacities [Nonempty A] [Nonempty B] :
    ∃ Cq Cp : ℝ, 0 ≤ Cq ∧ 0 ≤ Cp ∧ ∃ delta : ℝ, 0 < delta ∧ delta ≤ 2 ∧
      ∀ (E F : Type) [Fintype E] [DecidableEq E] [Nonempty E]
        [Fintype F] [DecidableEq F] [Nonempty F],
      ∀ (V : Matrix (B × E) A ℂ) (W : Matrix (A × F) B ℂ),
        IsIsometry V → IsIsometry W →
        (∀ rho : Matrix A A ℂ,
          traceRight (complementaryChannel (composedDilation V W) rho) = complementaryChannel V rho) ∧
        (∀ eps ∈ Set.Icc 0 2,
          diamond (channelDifference (receiverChannel W ∘ receiverChannel V) id) ≤ eps →
          diamond (channelDifference (complementaryChannel V) (recoveryDegrader V W ∘ receiverChannel V)) ≤
            2 * eps ^ (3 / 2 : ℝ)) ∧
        (∀ eps ∈ Set.Icc 0 delta,
          diamond (channelDifference (receiverChannel W ∘ receiverChannel V) id) ≤ eps →
          LowNoiseCapacityBounds V eps Cq Cp) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P50

end
