-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P24_entanglementBreakingRegion
-- name    : QAlgorithms.Papers.Independent.Claimed50.P24.entanglementBreakingRegion
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:40:23.472847+00:00
-- url     : https://prove2.me/theorems/20ee3778-8687-498f-915a-0220d3b7e664
-- title:
--   The private dynamic region of an entanglement-breaking channel
-- statement:
--   Let $\mathcal N:A'\to B$ be a channel on finite nonzero quantum registers, with one fixed isometric dilation $U:A'\to B\otimes E$. The complementary channel is $\mathcal N^c(\rho)=\operatorname{Tr}_B U\rho U^\dagger$. All entropies use base-two logarithms and $0\log 0=0$.
--
--   Let $\mathcal C(\mathcal N)\subseteq\mathbb R^3$ be the closure of net triples $(R,P,S)$ achievable with vanishing full trace-norm error by finite block protocols using independent channel copies, forward noiseless public and private classical communication, and initially uniform shared secret key. Generated and consumed rates are separately finite and fixed before the error tolerances. Positive net rates mean generation. The uniform private message and generated secret key must be jointly recovered and decoupled from all public data, the full channel environment, and explicitly discarded local systems. Local memory and operations are free; there is no feedback or prior entanglement.
--
--   Suppose $\mathcal N$ is entanglement breaking: applying it to one share of any finite-dimensional bipartite density matrix produces a separable state. Let
--   $$
--   C_1(\mathcal N)=\max_{\{p_X,\psi_x\}} I(X;B),\qquad \|\psi_x\|=1,
--   $$
--   where the pure input is sent through $\mathcal N$ and the finite-ensemble maximum is attained. Then
--   $$
--   \mathcal C(\mathcal N)=\{(R,P,S)\in\mathbb R^3:R+P\le C_1(\mathcal N),\ P+S\le0,\ R+P+S\le C_1(\mathcal N)\}.
--   $$
--   The same channel quantity bounds the first and third combinations. Resource consumption is allowed. This gives the single-letter operational region for this channel class.
-- source:
--   Public and private resource trade-offs for a quantum channel, arXiv:1005.3818v3, PDF p. 14, Theorem 3

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

/-- Theorem 3, PDF pp.14--15: the independently operational region of an
entanglement-breaking channel. The same attained pure-ensemble maximum occurs twice.
The printed sigma/omega change is a dummy-state typo. The p.8 correction is as in Theorem 1. -/
theorem entanglementBreakingRegion (V : Dilation I B E) (hV : PhysicalDilation V)
    (hEB : ChannelEB (receiverChannel V)) :
    ∃ c : ℝ, IsGreatest (pureSingleValues (infoXB V)) c ∧
      privateDynamicRegion V = {r | r 0 + r 1 ≤ c ∧ r 1 + r 2 ≤ 0 ∧ r 0 + r 1 + r 2 ≤ c} := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P24

end
