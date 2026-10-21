-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P24_hadamardSingleLetter
-- name    : QAlgorithms.Papers.Independent.Claimed50.P24.hadamardSingleLetter
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:45:28.661461+00:00
-- url     : https://prove2.me/theorems/4ea8875d-c822-445f-9580-8e97112887c9
-- title:
--   The Hadamard operational region is the literal one-use union
-- statement:
--   Let $\mathcal N:A'\to B$ be a channel on finite nonzero quantum registers, with one fixed isometric dilation $U:A'\to B\otimes E$. The complementary channel is $\mathcal N^c(\rho)=\operatorname{Tr}_B U\rho U^\dagger$. All entropies use base-two logarithms and $0\log 0=0$.
--
--   For any finite classical alphabets $X,Y$, probability distribution $p_{XY}$, and normalized density matrices $\rho_{xy}^{A'}$, write $\sigma^{XYBE}=\sum_{x,y}p_{XY}(x,y)|x,y\rangle\langle x,y|\otimes U\rho_{xy}U^\dagger$. Pure conditional states are allowed. A single-label ensemble is written $\{p_X(x),\rho_x\}$.
--
--   Let $\mathcal C(\mathcal N)\subseteq\mathbb R^3$ be the closure of net triples $(R,P,S)$ achievable with vanishing full trace-norm error by finite block protocols using independent channel copies, forward noiseless public and private classical communication, and initially uniform shared secret key. Generated and consumed rates are separately finite and fixed before the error tolerances. Positive net rates mean generation. The uniform private message and generated secret key must be jointly recovered and decoupled from all public data, the full channel environment, and explicitly discarded local systems. Local memory and operations are free; there is no feedback or prior entanglement.
--
--   Let $\mathcal C^{(1)}(\mathcal N)$ be the union, over the ensembles above, of triples satisfying the three inequalities
--   $$
--   R+P\le I(XY;B),\qquad P+S\le I(Y;B|X)-I(Y;E|X),\qquad R+P+S\le I(XY;B)-I(Y;E|X).
--   $$
--   If $\mathcal N^c$ is entanglement breaking, then
--   $$
--   \mathcal C^{(1)}(\mathcal N)\text{ is closed},\qquad \mathcal C(\mathcal N)=\mathcal C^{(1)}(\mathcal N).
--   $$
--   Thus the literal single-use union suffices, without adding an unmentioned closure or regularization.
-- source:
--   Public and private resource trade-offs for a quantum channel, arXiv:1005.3818v3, PDF p. 15, Section 8

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

/-- Section 8, PDF pp.15--17: literal single-use region equality for Hadamard channels.
Closedness is included explicitly, rather than silently replacing the union by its closure. -/
theorem hadamardSingleLetter (V : Dilation I B E) (hV : PhysicalDilation V) (hHad : Hadamard V) :
    IsClosed (oneUseRPSRegion V) ∧ privateDynamicRegion V = oneUseRPSRegion V := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P24

end
