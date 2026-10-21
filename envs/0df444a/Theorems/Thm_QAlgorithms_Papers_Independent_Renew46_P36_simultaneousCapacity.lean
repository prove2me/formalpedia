-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P36_simultaneousCapacity
-- name    : QAlgorithms.Papers.Independent.Renew46.P36.simultaneousCapacity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T22:03:17.133733+00:00
-- url     : https://prove2.me/theorems/eb66cc67-84a7-4247-a409-022f022b0458
-- title:
--   Theorem 1: simultaneous capacity region and alphabet bound
-- statement:
--   Let $\mathcal N$ be a completely positive trace-preserving map between finite, nonzero complex quantum registers $A'$ and $B$. Let $S_{\mathrm{Ia}},S_{\mathrm{Ib}},S_{\mathrm{II}}$ denote its unassisted simultaneous classical–quantum capacity regions for subspace transmission, entanglement transmission, and entanglement generation. Codes use the full tensor power of the channel, arbitrary positive integer message and logical dimensions, message-dependent encoders and a decoding instrument whose CP branches sum to a channel. Both errors are controlled for every message; Ia tests every logical pure state, Ib preserves half of a normalized maximally entangled state, and II uses message-dependent pure preparations. Fidelity is squared fidelity. A nonnegative rate pair is achievable when, for every positive error tolerance and rate slack, every sufficiently large block length admits such a code whose two logarithmic rates are at least the target rates minus the slack.
--
--   For a normalized finite pure ensemble $\{p_x,\phi_x^{AA'}\}$, with arbitrary finite reference $A$ and zero weights allowed, let $\sigma_x^{AB}=(\mathrm{id}_A\otimes\mathcal N)(\phi_x)$. In bits define $I(X;B)=H(\sum_xp_x\sigma_x^B)-\sum_xp_xH(\sigma_x^B)$ and $I(A\rangle BX)=\sum_xp_x[H(\sigma_x^B)-H(\sigma_x^{AB})]$, using the same ensemble in both expressions. Let $S^{(1)}(\mathcal N)$ be the union of the nonnegative rectangles bounded by these two quantities, and let $S^{(1)}_{\leq b}$ restrict the ensemble alphabet to at most $b$ letters. Then
--
--   $$
--   S_{\mathrm{Ia}}(\mathcal N)=S_{\mathrm{Ib}}(\mathcal N)=S_{\mathrm{II}}(\mathcal N)
--   =\overline{\bigcup_{\ell\geq1}\frac1\ell S^{(1)}(\mathcal N^{\otimes\ell})},\qquad
--   S^{(1)}(\mathcal N)=S^{(1)}_{\leq(\dim A')^2+2}(\mathcal N).
--   $$
--
--   This characterizes all three operational tasks and bounds the auxiliary alphabet without assuming finite-block attainment.
--
--   **Formalization Note** The closure corrects the missing overline in printed (5), in accordance with the limiting definition on page 2 and arbitrary-slack converse on page 7. The entropy sign follows the proofs rather than the reversed conditional-entropy sign printed on page 3.
-- source:
--   The capacity of a quantum channel for simultaneous transmission of classical and quantum information, arXiv:quant-ph/0311131v3, PDF p. 4, Theorem 1: simultaneous capacity region and alphabet bound

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P36

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Renew46.P36

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P08 (Ensemble canonicalPurification)

open QAlgorithms.Papers.Independent.Dependency50.P07 (Typical)

open QAlgorithms.Papers.Independent.Information100.P27 (qubitDephasing)

open QAlgorithms.Papers.Independent.Dependency50.P41 (maximallyEntangled)

open QAlgorithms.Papers.Independent.Claimed50.P20 (DynamicPureEnsemble pureOutputs cqHolevoBits conditionalCoherent)

open QAlgorithms.Papers.Independent.Information100.P67
  (IsDegradable receiverChannel complementaryChannel maximumCoherentInformation squaredFidelity)

open QAlgorithms.Papers.Independent.Information100.P76 (maximallyMixed)

open QAlgorithms.Papers.Independent.Information100.P80 (quantumCapacity)

open QAlgorithms.Papers.Independent.Next46.P40
  (dephasingIsometry generalizedDephasing diagonalPart)

variable {A B E A1 A2 E1 E2 : Type}

variable [Fintype A] [Fintype B] [Fintype E]

variable [Fintype A1] [Fintype A2] [Fintype E1] [Fintype E2]

/-- Theorem 1, PDF pp.2--4,7,15: all three operational equalities AND the alphabet
clause. Closed regularization corrects the missing overline in printed (5), using
the limiting achievability definition and arbitrary-delta converse. No finite-block
attainment or exact real log-integer rate is assumed. -/
theorem simultaneousCapacity
    [Nonempty A] [Nonempty B] (N : Superop A B) (hN : IsChannel N) :
    simultaneousOperationalRegion .Ia N = cqClosedRegularization N ∧
    simultaneousOperationalRegion .Ib N = cqClosedRegularization N ∧
    simultaneousOperationalRegion .II N = cqClosedRegularization N ∧
    cqOneLetterRegion N = boundedAlphabetRegion N (Fintype.card A ^ 2 + 2) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P36

end
