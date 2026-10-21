-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P24_completelyDephasingRegion
-- name    : QAlgorithms.Papers.Independent.Claimed50.P24.completelyDephasingRegion
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:43:09.726963+00:00
-- url     : https://prove2.me/theorems/397cd277-b65d-4ac9-90bc-0c10fbe26ba9
-- title:
--   The completely dephasing qubit region
-- statement:
--   Let $\mathcal C(\mathcal N)\subseteq\mathbb R^3$ be the closure of net triples $(R,P,S)$ achievable with vanishing full trace-norm error by finite block protocols using independent channel copies, forward noiseless public and private classical communication, and initially uniform shared secret key. Generated and consumed rates are separately finite and fixed before the error tolerances. Positive net rates mean generation. The uniform private message and generated secret key must be jointly recovered and decoupled from all public data, the full channel environment, and explicitly discarded local systems. Local memory and operations are free; there is no feedback or prior entanglement.
--
--   For the completely dephasing qubit channel $\Delta(\rho)=\sum_{i=0}^1\langle i|\rho|i\rangle|i\rangle\langle i|$,
--   $$
--   \mathcal C(\Delta)=\{(R,P,S)\in\mathbb R^3:R+P\le1,\ P+S\le0,\ R+P+S\le1\}.
--   $$
--   The qubit input fixes the public capacity at one bit per use. This example specializes the entanglement-breaking region while retaining consuming rates.
-- source:
--   Public and private resource trade-offs for a quantum channel, arXiv:1005.3818v3, PDF p. 15, Example 1

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P24

noncomputable section

open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Claimed50.P24

open QAlgorithms.Papers.Independent.Information100.P67
  (IsIsometry receiverChannel complementaryChannel erasureDilation)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I B E J D F : Type}

variable [Fintype I] [Fintype B] [Fintype E] [Fintype J] [Fintype D] [Fintype F]

variable [DecidableEq I] [DecidableEq B] [DecidableEq E]

variable [DecidableEq J] [DecidableEq D] [DecidableEq F]

variable [Nonempty I] [Nonempty B] [Nonempty E]

variable [Nonempty J] [Nonempty D] [Nonempty F]

/-- Example 1, PDF p.15: completely dephasing on a qubit, hence one public bit per use.
Uses the same corrected operational convention as Theorem 1. -/
theorem completelyDephasingRegion :
    privateDynamicRegion (dephasingDilation 1) =
      {r | r 0 + r 1 ≤ 1 ∧ r 1 + r 2 ≤ 0 ∧ r 0 + r 1 + r 2 ≤ 1} := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P24

end
