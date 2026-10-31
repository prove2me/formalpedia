-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P69_oneRound_recycling
-- name    : QAlgorithms.Papers.Independent.Intake100.P69.oneRound_recycling
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:26:12.407227+00:00
-- url     : https://prove2.me/theorems/6dd93cd8-3af6-4666-8f8e-d7d47a217720
-- title:
--   One-round recycling preserves the entire resource to first order
-- statement:
--   For a positive integer $N$, Alice and Bob share $N$ normalized qubit singlets, and Alice has one additional singlet half $A_0$ with inaccessible reference $R_0$. Put $\sigma_i=2^{-(N-1)}P^-_{A_0A_i}\otimes I$, $\rho=\sum_i\sigma_i$, and $E_i=\rho^{-1/2}\sigma_i\rho^{-1/2}$, with inverse on the support. The measurement uses the positive square roots $\sqrt{E_i}$. Write $v_i$ for its subnormalized full branch and $\xi_i$ for the normalized product of singlets on $A_0A_i$, $R_0B_i$, and all unused $A_jB_j$. The conclusive average root fidelity is $F_1(N)=\sum_i\|v_i\|\,|\langle\xi_i,v_i\rangle|$.
--
--   There are constants $C>0$ and an integer $N_0\ge1$ such that, for every integer $N\ge N_0$,
--
--   $$
--   F_1(N)\ge 1-\frac{11}{4N}-\frac{C}{N^2}.
--   $$
--
--   The comparison retains all unused ports. It also bounds any completion with a nonnegative failure-fidelity contribution. This states the one-sided meaning of the source's remainder, without claiming an exact finite bound or a two-sided expansion.
-- source:
--   Generalized teleportation and entanglement recycling, arXiv:1209.2683v2, PDF p. 3, Theorem 1, eq. (4): one-round recycling of the entire resource

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P69

namespace QAlgorithms.Papers.Independent.Intake100.P69

open scoped ComplexConjugate

open Filter

/-- PDF p.3, Theorem 1, (4), interpreted by p.6, (18)-(25): the conclusive
full-resource root fidelity has the printed one-sided second-order lower bound.
The universal remainder constant and threshold precede N. The normalized p.3
ideal product is used instead of the misnormalized vector in (20), p.6. -/
theorem oneRound_recycling :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, 1 ≤ N0 ∧
      ∀ N : ℕ, N0 ≤ N →
        1 - 11 / (4 * (N : ℝ)) - C / (N : ℝ) ^ 2 ≤ recyclingFidelity N := by sorry

end QAlgorithms.Papers.Independent.Intake100.P69
