-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P24_qubitErasureRegion
-- name    : QAlgorithms.Papers.Independent.Claimed50.P24.qubitErasureRegion
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:47:15.714691+00:00
-- url     : https://prove2.me/theorems/de27be85-1555-47f4-9f61-89d9a6f521be
-- title:
--   The analytic qubit erasure region for the full probability range
-- statement:
--   Let $\mathcal C(\mathcal N)\subseteq\mathbb R^3$ be the closure of net triples $(R,P,S)$ achievable with vanishing full trace-norm error by finite block protocols using independent channel copies, forward noiseless public and private classical communication, and initially uniform shared secret key. Generated and consumed rates are separately finite and fixed before the error tolerances. Positive net rates mean generation. The uniform private message and generated secret key must be jointly recovered and decoupled from all public data, the full channel environment, and explicitly discarded local systems. Local memory and operations are free; there is no feedback or prior entanglement.
--
--   For $\epsilon\in[0,1]$, let $\mathcal N_\epsilon$ be the qubit erasure channel: with probability $1-\epsilon$ the input is delivered to Bob and Eve receives an orthogonal flag, and with probability $\epsilon$ the input is delivered to Eve and Bob receives that flag. Let $H_2$ be binary entropy in bits. Then a real triple is in $\mathcal C(\mathcal N_\epsilon)$ exactly when there is one $p\in[0,1/2]$ such that
--   $$
--   R+P\le1-\epsilon,\qquad P+S\le(1-2\epsilon)H_2(p),\qquad R+P+S\le1-\epsilon-\epsilon H_2(p).
--   $$
--   The full probability range is included. In the antidegradable range $\epsilon\ge1/2$, the $p=0$ endpoint dominates. This is not a claim that all erasure channels are degradable.
-- source:
--   Public and private resource trade-offs for a quantum channel, arXiv:1005.3818v3, PDF p. 19, Theorem 6

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

/-- Theorem 6, PDF p.19 (proof pp.22--24): qubit erasure, full probability range.
The proof's blanket claim of degradability is corrected: eps >= 1/2 is handled by
antidegradability and the p=0 endpoint. No extra eps <= 1/2 hypothesis is inserted. -/
theorem qubitErasureRegion (eps : ℝ) (he0 : 0 ≤ eps) (he1 : eps ≤ 1) :
    privateDynamicRegion (erasureDilation (A := Fin 2) eps) = erasureRegion eps := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P24

end
