-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P50_quditPauli_quadraticDegradability
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P50.quditPauli_quadraticDegradability
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:58:14.83548+00:00
-- url     : https://prove2.me/theorems/13814ffd-cc6e-435b-b556-655347636e7b
-- title:
--   §4 unnumbered main result: quadratic degradability for generalized qudit Pauli channels
-- statement:
--   Fix an integer dimension $d\ge1$. In the standard basis define $X|j\rangle=|j+1\pmod d\rangle$ and $Z|j\rangle=e^{2\pi i j/d}|j\rangle$. For any probability distribution $w_{k\ell}$ on $0\le k,\ell<d$, let $N_w(\rho)=\sum_{k,\ell}w_{k\ell}X^kZ^\ell\rho(X^kZ^\ell)^\dagger$ and use its canonical Kraus-label dilation. There exist $C_d\ge0$ and $0<\delta_d\le2$ such that, uniformly over $w$,
--   $$
--   \|N_w-\mathrm{id}_d\|_\diamond\le\varepsilon\le\delta_d
--   \quad\Longrightarrow\quad
--   \operatorname{dg}(N_w)\le C_d\varepsilon^2\qquad(\varepsilon\ge0).
--   $$
--   The degradability parameter optimizes the full diamond error over all CPTP degrading maps. This is the stated class-level improvement for generalized Pauli noise; no polynomial-family hypothesis or dimension-independent constant is imposed.
-- source:
--   Quantum and private capacities of low-noise channels, arXiv:1705.04335v3, PDF p. 12, §4 unnumbered main result: quadratic degradability for generalized qudit Pauli channels

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

/-- §4 unnumbered main result, PDF pp.12,19: dimension-dependent but channel-uniform
quadratic bound for ALL generalized Pauli probability distributions near identity. -/
theorem quditPauli_quadraticDegradability (d : ℕ) (hd : 0 < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ delta : ℝ, 0 < delta ∧ delta ≤ 2 ∧
      ∀ w : (Fin d × Fin d) → ℝ, Probabilities w →
      ∀ eps ∈ Set.Icc 0 delta,
        diamond (channelDifference (receiverChannel (quditPauliDilation d w)) id) ≤ eps →
        degradability (quditPauliDilation d w) ≤ C * eps ^ 2 := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P50

end
