-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P40_channelInformationIdentities
-- name    : QAlgorithms.Papers.Independent.Claimed50.P40.channelInformationIdentities
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:47:51.517173+00:00
-- url     : https://prove2.me/theorems/1fd47c9a-ee6c-4c48-8e2e-03375622bdcb
-- title:
--   Independent-input channel-information identities
-- statement:
--   Let $W$ be a finite-dimensional classical-input channel with $s\ge1$ finite nonempty sender alphabets and independent input law $P=\bigotimes_iP_i$. Its classical-quantum channel state is $\gamma=\sum_x P(x)|x\rangle\langle x|\otimes W_x$. For any subset $J\subseteq[s]$, including the empty and full subsets,
--   $$
--   \begin{aligned}
--   I_\gamma(X(J):Y\mid X(J^c))
--   &=I_\gamma(X(J):YX(J^c))\\
--   &=H_\gamma(Y\mid X(J^c))-H_\gamma(Y\mid X([s]))\\
--   &=H(P_JW\mid P_{J^c})-H(W\mid P_{[s]}).
--   \end{aligned}
--   $$
--   Here $P_JW$ averages the channel over precisely the senders in $J$; its remaining argument is indexed by $J^c$. For a channel $V$ and input law $Q$, $H(V\mid Q)=\sum_aQ(a)H(V_a)$. Entropy uses the intrinsic algebra trace and base-two logarithms.
--
--   These identities connect the entropy-of-marginals definition of conditional information to the averaged-channel formula used in the capacity bounds. All terms are computed from $W,P$, rather than introduced as variables constrained by the asserted equalities.
-- source:
--   The Capacity of the Quantum Multiple Access Channel, arXiv:quant-ph/9807019v3, PDF p. 3, §III, channel-state identities

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P40

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Claimed50.P40

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Channel-information calculus, PDF p.3: all four expressions are computed from the
same independent-input channel state; P_J W averages J, leaving J-complement. -/
theorem channelInformationIdentities {s : ℕ} (C : ClassicalChannel s)
    (P : InputLaw C.alphabet) (J : Finset (Fin s)) :
    conditionalInformation C.state P J = senderOutputMutualInformation C.state P J Jᶜ ∧
    conditionalInformation C.state P J =
      conditionalOutputEntropy C.state P Jᶜ -
        conditionalOutputEntropy C.state P Finset.univ ∧
    conditionalInformation C.state P J =
      averagedChannelEntropy C.state P J - meanOutputEntropy C.state P := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P40

end
