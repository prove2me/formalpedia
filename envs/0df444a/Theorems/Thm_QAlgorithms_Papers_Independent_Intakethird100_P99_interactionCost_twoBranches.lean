-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P99_interactionCost_twoBranches
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P99.interactionCost_twoBranches
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:47:03.534877+00:00
-- url     : https://prove2.me/theorems/0b478e75-126a-4d6b-9239-be75d60b9cc8
-- title:
--   Result 2: the two-branch attained interaction cost
-- statement:
--   Let $H$ be a Hermitian Hamiltonian on two qubits $A,B$, with canonical interaction coefficients $\alpha=(\alpha_1,\alpha_2,\alpha_3)$ satisfying $\alpha_1\ge\alpha_2\ge|\alpha_3|$. Local terms in $H$ are allowed. Local unitary controls are instantaneous and free, interaction intervals are nonnegative, and $\hbar=1$. Write $C_H(U)$ for the infimum of the interaction durations of protocols implementing the gate $U$, allowing the ideal limit of arbitrarily fine pulses at fixed total duration and disregarding global phase. This cost is an extended nonnegative real, with value $+\infty$ for an impossible simulation. For a two-qubit unitary $U$, let $\beta$ be an actual interaction-content witness: $U$ is locally equivalent, up to global phase, to $U_\beta=\exp[-i\sum_{k=1}^3\beta_k\sigma_k\otimes\sigma_k]$, where $\sigma_1,\sigma_2,\sigma_3$ are the Pauli matrices $X,Y,Z$ and $\pi/4\ge\beta_1\ge\beta_2\ge|\beta_3|$. For real triples, $x\prec_s y$ means s-majorization: sort their absolute coordinates in descending order, give the smallest coordinate the sign of the product, and compare the first coordinate and the two sums $x_1+x_2\mp x_3$. Put $\beta_n=\beta+(\pi/2)n$ for $n\in\mathbb Z^3$. If $\alpha_1>0$, there is a least feasible time $t_*$, attained in the ideal control model, such that
--
--   $$C_H(U)=t_* = \min\{t\ge0:\beta\prec_s t\alpha\ \text{or}\ \beta_{(-1,0,0)}\prec_s t\alpha\}.$$
--
--   For zero canonical interaction, the cost is $0$ for local gates and $+\infty$ otherwise. This characterizes time cost using just two periodic branches.
-- source:
--   Characterization of non-local gates, arXiv:quant-ph/0205100v3, PDF p. 6, Result 2: interaction cost; main result selected from the p.1 abstract

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P99

namespace QAlgorithms.Papers.Independent.Intakethird100.P99

open scoped Matrix Kronecker NNReal ENNReal

open QAlgorithms.Papers.Independent.Information100.P10 (pauli)

open QAlgorithms.Papers.Independent.Information100.P32 (evolution)

noncomputable section

/-- PDF p.6, Result 2 (abstract p.1): the two-branch minimum is attained for a nonzero
interaction. For a zero canonical interaction the extended cost is 0 on local gates and
infinity otherwise; no division by zero or empty real infimum is used. -/
theorem interactionCost_twoBranches (H U : TwoMatrix) (a b : Triple)
    (hH : HasCanonicalHamiltonian H a) (hU : HasContent U b) :
    (0 < a 0 → ∃ t : ℝ, IsLeast {s : ℝ | 0 ≤ s ∧
        (SMajorized b (s • a) ∨ SMajorized (secondShift b) (s • a))} t ∧
      IdealSimulates H U t ∧ interactionCost H U = ENNReal.ofReal t) ∧
    (a = 0 → (TwoQubitLocalEquivalent U 1 → interactionCost H U = 0) ∧
      (¬ TwoQubitLocalEquivalent U 1 → interactionCost H U = ⊤)) := by sorry

end

end QAlgorithms.Papers.Independent.Intakethird100.P99
