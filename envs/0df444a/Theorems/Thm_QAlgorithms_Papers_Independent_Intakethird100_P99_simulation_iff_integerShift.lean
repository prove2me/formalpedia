-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P99_simulation_iff_integerShift
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P99.simulation_iff_integerShift
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:47:50.156413+00:00
-- url     : https://prove2.me/theorems/72331431-9ca7-435f-ab43-2d2a40630b05
-- title:
--   Result 1: necessary and sufficient fast-control simulation
-- statement:
--   Let $H$ be a Hermitian Hamiltonian on two qubits $A,B$, with canonical interaction coefficients $\alpha=(\alpha_1,\alpha_2,\alpha_3)$ satisfying $\alpha_1\ge\alpha_2\ge|\alpha_3|$. Local terms in $H$ are allowed. Local unitary controls are instantaneous and free, interaction intervals are nonnegative, and $\hbar=1$. Write $C_H(U)$ for the infimum of the interaction durations of protocols implementing the gate $U$, allowing the ideal limit of arbitrarily fine pulses at fixed total duration and disregarding global phase. This cost is an extended nonnegative real, with value $+\infty$ for an impossible simulation. For a two-qubit unitary $U$, let $\beta$ be an actual interaction-content witness: $U$ is locally equivalent, up to global phase, to $U_\beta=\exp[-i\sum_{k=1}^3\beta_k\sigma_k\otimes\sigma_k]$, where $\sigma_1,\sigma_2,\sigma_3$ are the Pauli matrices $X,Y,Z$ and $\pi/4\ge\beta_1\ge\beta_2\ge|\beta_3|$. For real triples, $x\prec_s y$ means s-majorization: sort their absolute coordinates in descending order, give the smallest coordinate the sign of the product, and compare the first coordinate and the two sums $x_1+x_2\mp x_3$. For every $t\ge0$,
--
--   $$U\text{ is ideally simulable using }H\text{ for total time }t\quad\Longleftrightarrow\quad\exists n\in\mathbb Z^3,\ \beta+(\pi/2)n\prec_s t\alpha.$$
--
--   The protocol is an operator protocol uniform over all input states. This is a two-way feasibility characterization, including $t=0$.
-- source:
--   Characterization of non-local gates, arXiv:quant-ph/0205100v3, PDF p. 4, Result 1: necessary and sufficient gate simulation condition

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P99

namespace QAlgorithms.Papers.Independent.Intakethird100.P99

open scoped Matrix Kronecker NNReal ENNReal

open QAlgorithms.Papers.Independent.Information100.P10 (pauli)

open QAlgorithms.Papers.Independent.Information100.P32 (evolution)

noncomputable section

/-- PDF pp.4–6, Result 1: exact ideal fast-control feasibility iff some integer shift is
s-majorized by the available canonical interaction-time vector, also at time zero. -/
theorem simulation_iff_integerShift (H U : TwoMatrix) (a b : Triple) (t : ℝ)
    (hH : HasCanonicalHamiltonian H a) (hU : HasContent U b) (ht : 0 ≤ t) :
    IdealSimulates H U t ↔ ∃ n : Fin 3 → ℤ, SMajorized (contentIntegerShift b n) (t • a) := by sorry

end

end QAlgorithms.Papers.Independent.Intakethird100.P99
