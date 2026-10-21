-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P26_identity_success_bound
-- name    : QAlgorithms.Papers.Independent.Claimed50.P26.identity_success_bound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:09:10.250326+00:00
-- url     : https://prove2.me/theorems/ecb02a08-d76b-43b5-a938-6edba8849f3e
-- title:
--   Unnumbered qubit identity-channel success bound
-- statement:
--   Let $n\ge0$ and $M\ge1$ be integers. Encode a uniform message in $\{1,\ldots,M\}$ by arbitrary density matrices $\rho_x$ on $n$ qubits and decode after the identity channel by any POVM $\{E_x\}_{x=1}^M$. Then
--
--   $$
--   P_{\rm succ}=\frac1M\sum_{x=1}^M\operatorname{Tr}(E_x\rho_x)
--   \le\frac{2^n}{M}.
--   $$
--
--   When $M=2^{nR}$, the upper bound is $2^{-n(R-1)}$. At $n=0$ the channel is scalar and the bound is $1/M$. This elementary dimension bound includes all mixed and entangled block codewords.
-- source:
--   A strong converse for classical channel coding using entangled inputs, arXiv:0903.2838v1, PDF p. 1, Unnumbered qubit identity-channel success bound

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P26

noncomputable section

open scoped Matrix ComplexOrder ComplexConjugate Topology

open Filter

namespace QAlgorithms.Papers.Independent.Claimed50.P26

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P08 (Ensemble ensembleAverage depolarizing)

open QAlgorithms.Papers.Independent.Information100.P71
  (supportPower channelPower)

open QAlgorithms.Papers.Independent.Dependency50.P23
  (UACode uaCodeSuccess uaSuccess ordinaryClassicalCapacity)

open QAlgorithms.Papers.Independent.Information100.P60 (wernerHolevo)

open QAlgorithms.Papers.Independent.Dependency50.P35 (renyiEntropy petz relative)

open QAlgorithms.Papers.Independent.Dependency50.P24 (cqState)

/-- PDF p.1, unnumbered identity-channel calculation: arbitrary mixed, possibly
entangled n-qubit codewords, every decoder, and uniform integer message count.
Includes n=0, when success is at most 1/M. -/
theorem identity_success_bound (n M : ℕ) (hM : 0 < M)
    (K : UACode (Fin n → Fin 2) (Fin n → Fin 2) M) :
    uaCodeSuccess (fun X => X) K ≤ (2 : ℝ)^n / M := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P26

end
