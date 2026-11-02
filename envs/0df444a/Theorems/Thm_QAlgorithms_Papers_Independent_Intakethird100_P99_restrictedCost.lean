-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P99_restrictedCost
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P99.restrictedCost
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:51:49.20521+00:00
-- url     : https://prove2.me/theorems/e8bf24b1-9466-4894-aebc-7e24f2560c18
-- title:
--   The exact restricted-chamber criterion and one-branch cost
-- statement:
--   Let $H$ be a Hermitian Hamiltonian on two qubits $A,B$, with canonical interaction coefficients $\alpha=(\alpha_1,\alpha_2,\alpha_3)$ satisfying $\alpha_1\ge\alpha_2\ge|\alpha_3|$. Local terms in $H$ are allowed. Local unitary controls are instantaneous and free, interaction intervals are nonnegative, and $\hbar=1$. Write $C_H(U)$ for the infimum of the interaction durations of protocols implementing the gate $U$, allowing the ideal limit of arbitrarily fine pulses at fixed total duration and disregarding global phase. This cost is an extended nonnegative real, with value $+\infty$ for an impossible simulation. For a two-qubit unitary $U$, let $\beta$ be an actual interaction-content witness: $U$ is locally equivalent, up to global phase, to $U_\beta=\exp[-i\sum_{k=1}^3\beta_k\sigma_k\otimes\sigma_k]$, where $\sigma_1,\sigma_2,\sigma_3$ are the Pauli matrices $X,Y,Z$ and $\pi/4\ge\beta_1\ge\beta_2\ge|\beta_3|$. For real triples, $x\prec_s y$ means s-majorization: sort their absolute coordinates in descending order, give the smallest coordinate the sign of the product, and compare the first coordinate and the two sums $x_1+x_2\mp x_3$. Write $\beta^- =\beta-(\pi/2,0,0)$. For a nonzero interaction ($\alpha_1>0$),
--
--   $$\beta\prec_s\beta^-\quad\Longleftrightarrow\quad\beta_1+|\beta_3|\le\pi/4.$$
--
--   Under this restriction, $C_H(U)=\min\{t\ge0:\beta\prec_s t\alpha\}$, with the minimum attained in the ideal control model. The shifted vector is s-ordered before comparison, giving $(\pi/2-\beta_1,\beta_2,-\beta_3)$.
-- source:
--   Characterization of non-local gates, arXiv:quant-ph/0205100v3, PDF p. 6, III.C: when the second shift can be omitted

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P99

namespace QAlgorithms.Papers.Independent.Intakethird100.P99

open scoped Matrix Kronecker NNReal ENNReal

open QAlgorithms.Papers.Independent.Information100.P10 (pauli)

open QAlgorithms.Papers.Independent.Information100.P32 (evolution)

noncomputable section

/-- PDF pp.6–7, III.C: the exact criterion for dropping the second branch, and the
resulting attained one-branch interaction-cost formula. -/
theorem restrictedCost (H U : TwoMatrix) (a b : Triple)
    (hH : HasCanonicalHamiltonian H a) (hU : HasContent U b) (ha : 0 < a 0) :
    (SMajorized b (secondShift b) ↔ b 0 + |b 2| ≤ Real.pi / 4) ∧
    (b 0 + |b 2| ≤ Real.pi / 4 → ∃ t : ℝ,
      IsLeast {s : ℝ | 0 ≤ s ∧ SMajorized b (s • a)} t ∧
      IdealSimulates H U t ∧ interactionCost H U = ENNReal.ofReal t) := by sorry

end

end QAlgorithms.Papers.Independent.Intakethird100.P99
