-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P50_complement_approximately_degrades
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P50.complement_approximately_degrades
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:56:11.254244+00:00
-- url     : https://prove2.me/theorems/5992da98-e1fd-430d-9c7c-8d2d80e0fef6
-- title:
--   Theorem 11: the complement itself approximately degrades a low-noise channel
-- statement:
--   Let $N:A\to A$ be a quantum channel on a nonzero finite-dimensional system, and fix any isometric dilation and its full complement $N^c$. If $0\le\varepsilon\le2$ and $\|N-\mathrm{id}_A\|_\diamond\le\varepsilon$, then the specified degrading map $N^c$ satisfies
--   $$
--   \|N^c-N^c\circ N\|_\diamond\le2\varepsilon^{3/2}.
--   $$
--   This retains the constructive approximate degrader, including the exact zero-noise endpoint. It is the explicit norm inequality on the full stated parameter interval.
-- source:
--   Quantum and private capacities of low-noise channels, arXiv:1705.04335v3, PDF p. 11, Theorem 11: the complement itself approximately degrades a low-noise channel

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

/-- Theorem 11, PDF p.11: the SPECIFIED degrader is N^c itself. The norm bound
holds on the full [0,2] interval; no inadmissible degradability parameter is introduced. -/
theorem complement_approximately_degrades [Nonempty A] [Nonempty E]
    (V : Matrix (A × E) A ℂ) (hV : IsIsometry V)
    (eps : ℝ) (heps : eps ∈ Set.Icc 0 2)
    (hclose : diamond (channelDifference (receiverChannel V) id) ≤ eps) :
    diamond (channelDifference (complementaryChannel V) (complementaryChannel V ∘ receiverChannel V)) ≤
      2 * eps ^ (3 / 2 : ℝ) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P50

end
