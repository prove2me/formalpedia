-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P24_cloningRegion
-- name    : QAlgorithms.Papers.Independent.Claimed50.P24.cloningRegion
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:46:44.335063+00:00
-- url     : https://prove2.me/theorems/934b05cd-8663-4888-803e-e71b1f3041b9
-- title:
--   The analytic universal one-to-N cloning region
-- statement:
--   Let $\mathcal C(\mathcal N)\subseteq\mathbb R^3$ be the closure of net triples $(R,P,S)$ achievable with vanishing full trace-norm error by finite block protocols using independent channel copies, forward noiseless public and private classical communication, and initially uniform shared secret key. Generated and consumed rates are separately finite and fixed before the error tolerances. Positive net rates mean generation. The uniform private message and generated secret key must be jointly recovered and decoupled from all public data, the full channel environment, and explicitly discarded local systems. Local memory and operations are free; there is no feedback or prior entanglement.
--
--   Let $N\ge1$ be an integer, and let $\mathcal N_{\mathrm{Cl}}$ be the universal $1\to N$ qubit cloning channel, with all clones delivered to Bob and the complementary output to Eve. Define $\Delta_N=N(N+1)/2$ and, for a common $\nu\in[0,1/2]$,
--   $$
--   a_i(\nu)=\frac{(N-2i)\nu+i}{\Delta_N}\quad(0\le i\le N),\qquad
--   b_i(\nu)=\frac{(N-1-2i)\nu+i+1}{\Delta_N}\quad(0\le i\le N-1).
--   $$
--   Let $H(q)=-\sum_iq_i\log_2q_i$ and $C_N=1-\log_2N+\Delta_N^{-1}\sum_{i=0}^Ni\log_2i$. Then membership in the operational region is equivalent to existence of one such $\nu$ satisfying
--   $$
--   R+P\le C_N,\qquad P+S\le H(a(\nu))-H(b(\nu)),\qquad R+P+S\le\log_2(N+1)-H(b(\nu)).
--   $$
--   This uses the full symmetric output space of all clones. The boundary parameter is distinct from the supporting multiplier $\mu$.
-- source:
--   Public and private resource trade-offs for a quantum channel, arXiv:1005.3818v3, PDF p. 18, Theorem 5

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

/-- Theorem 5, PDF p.18 (proof pp.21--22): N >= 1, all clones go to Bob, and one common
boundary eigenvalue parameter nu appears in both entropy differences. It is distinct from mu. -/
theorem cloningRegion (N : ℕ) (hN : 0 < N) :
    privateDynamicRegion (cloningDilation N) = {r | ∃ nu : ℝ, nu ∈ Set.Icc 0 (1 / 2) ∧
      r 0 + r 1 ≤ cloningPublic N ∧
      r 1 + r 2 ≤ distributionEntropy (cloningLambda N nu) -
        distributionEntropy (cloningEta N nu) ∧
      r 0 + r 1 + r 2 ≤ Real.logb 2 (N + 1 : ℕ) -
        distributionEntropy (cloningEta N nu)} := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P24

end
