-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P07_depolarizing_ssPrivateCapacity_bound
-- name    : QAlgorithms.Papers.Independent.Support50.P07.depolarizing_ssPrivateCapacity_bound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T18:58:39.95684+00:00
-- url     : https://prove2.me/theorems/3d10ac3e-b645-46df-a97a-eeb907cb4c68
-- title:
--   Section IV.C: symmetric-assisted depolarizing capacity bound
-- statement:
--   For $p\in[0,1]$, let $\mathcal N_p(\rho)=(1-p)\rho+\frac p3(X\rho X+Y\rho Y+Z\rho Z)$, let $\eta_p=4\sqrt{1-p}(1-\sqrt{1-p})$, and set $f(\gamma)=\sup_{0\le t\le1}[H(t(1-\gamma))-H(t\gamma)]$. Let $g(p)=\min\{1-H(p),f(\eta_p),\max(1-4p,0)\}$. Write $\operatorname{conv}g$ for the lower convex envelope on $[0,1]$, namely the infimum of $\sum_i w_i g(p_i)$ over finite nonnegative weights summing to one with $p_i\in[0,1]$ and $\sum_i w_ip_i=p$. Then
--
--   $$C_{p,ss}(\mathcal N_p)\le (\operatorname{conv}g)(p).$$
--
--   Here $p$ is total Pauli error; the QBER is $2p/3$.
--
--   All quantum registers are finite and nonzero, states have trace one, pure vectors have norm one, and entropy and logarithms are in bits. Operational private capacities use memoryless powers, positive blocklengths and message counts, uniform messages, arbitrary mixed block inputs, and normalized decoding POVMs. A code is good when its joint decoded message/environment state has full trace norm less than the error from a perfectly correlated uniform pair tensor its actual common environment marginal. Rates use every positive error and rate slack at all sufficiently large blocklengths. Symmetric assistance allows one arbitrary finite symmetric channel per block without charging its dimension.
--
--   This result supplies a capacity identity or bound for the channel family and resource model stated above.
--
--   The same bound on the unassisted capacity, $C_p(\mathcal N_p)\le\operatorname{conv}(g)(p)$, is included explicitly.
-- source:
--   The private classical capacity with a symmetric side channel and its application to quantum cryptography, arXiv:0705.3838v1, PDF p. 6, Section IV.C: symmetric-assisted depolarizing capacity bound

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P07

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Support50.P07

open QAlgorithms.Papers.Independent.Information100.P67
  (IsIsometry receiverChannel complementaryChannel IsDegradable IsAntidegradable
    dilationPower idealJoint maximumCoherentInformation)

open QAlgorithms.Papers.Independent.Claimed50.P24 (productDilation)

open QAlgorithms.Papers.Independent.Dependency50.P19 (mutualInformation)

variable {A B E C D F : Type}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype E] [DecidableEq E] [Fintype C] [DecidableEq C]

variable [Fintype D] [DecidableEq D] [Fintype F] [DecidableEq F]

/-- Section IV.C, PDF pp.6–7: convex envelope of the three displayed ss bounds.
Here p is total Pauli error, not QBER. Above p=1/4 the zero bound suffices, including
where the low-noise damping decomposition no longer applies. -/
theorem depolarizing_ssPrivateCapacity_bound [Nonempty E]
    (U : Matrix (Fin 2 × E) (Fin 2) ℂ)
    (hU : IsIsometry U) (p : ℝ) (hp : p ∈ Set.Icc 0 1)
    (hmap : receiverChannel U = depolarizingChannel p) :
    ssPrivateCapacity U ≤ depolarizingEnvelope p ∧
    fullTracePrivateCapacity U ≤ depolarizingEnvelope p := by sorry

end QAlgorithms.Papers.Independent.Support50.P07

end
