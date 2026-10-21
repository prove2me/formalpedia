-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P24_privateDynamicCapacity
-- name    : QAlgorithms.Papers.Independent.Claimed50.P24.privateDynamicCapacity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:32:35.62141+00:00
-- url     : https://prove2.me/theorems/560ef682-7f62-4a59-8df1-4a8d2b54c6f9
-- title:
--   Private dynamic capacity: operational region equals the regularized entropic region
-- statement:
--   Let $\mathcal N:A'\to B$ be a channel on finite nonzero quantum registers, with one fixed isometric dilation $U:A'\to B\otimes E$. The complementary channel is $\mathcal N^c(\rho)=\operatorname{Tr}_B U\rho U^\dagger$. All entropies use base-two logarithms and $0\log 0=0$.
--
--   For any finite classical alphabets $X,Y$, probability distribution $p_{XY}$, and normalized density matrices $\rho_{xy}^{A'}$, write $\sigma^{XYBE}=\sum_{x,y}p_{XY}(x,y)|x,y\rangle\langle x,y|\otimes U\rho_{xy}U^\dagger$. Pure conditional states are allowed. A single-label ensemble is written $\{p_X(x),\rho_x\}$.
--
--   Let $\mathcal C(\mathcal N)\subseteq\mathbb R^3$ be the closure of net triples $(R,P,S)$ achievable with vanishing full trace-norm error by finite block protocols using independent channel copies, forward noiseless public and private classical communication, and initially uniform shared secret key. Generated and consumed rates are separately finite and fixed before the error tolerances. Positive net rates mean generation. The uniform private message and generated secret key must be jointly recovered and decoupled from all public data, the full channel environment, and explicitly discarded local systems. Local memory and operations are free; there is no feedback or prior entanglement.
--
--   For one ensemble $\sigma$, let $\mathcal C^{(1)}_\sigma(\mathcal N)$ consist of all real triples satisfying
--   $$
--   R+P\le I(XY;B)_\sigma,\qquad
--   P+S\le I(Y;B|X)_\sigma-I(Y;E|X)_\sigma,\qquad
--   R+P+S\le I(XY;B)_\sigma-I(Y;E|X)_\sigma.
--   $$
--   Let $\mathcal C^{(1)}(\mathcal N)$ be the union over all such ensembles. Then
--   $$
--   \mathcal C(\mathcal N)=\overline{\bigcup_{k\ge1}\frac1k\mathcal C^{(1)}(\mathcal N^{\otimes k})}.
--   $$
--   The $k$-use input states may be entangled across channel uses. This identifies an independently defined operational region with an entropic regularization.
--
--   **Formalization Note** The final security condition uses the operational resource meaning in Section 2 and Figure 1. The stronger pre-decoding product condition on page 8 would exclude explicitly allowed resource conversions and is not imposed.
-- source:
--   Public and private resource trade-offs for a quantum channel, arXiv:1005.3818v3, PDF p. 5, Theorem 1

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

/-- Theorem 1, PDF p.5, with protocol definitions from pp.4,7--8.
Correction: final joint recovery/secrecy replaces p.8's excessive independence of
consumed/private registers; Eve includes local dumps omitted in the printed marginals.
The RHS is the closure of the positive-blocklength, rescaled literal one-use unions. -/
theorem privateDynamicCapacity (V : Dilation I B E) (hV : PhysicalDilation V) :
    privateDynamicRegion V = closure {r : Rate | ∃ n : ℕ, 0 < n ∧
      (fun i => (n : ℝ) * r i) ∈ oneUseRPSRegion (powerDilation V n)} := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P24

end
