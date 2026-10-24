-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P39_clippedCoherentCapacity
-- name    : QAlgorithms.Papers.Independent.Support50.P39.clippedCoherentCapacity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T21:59:04.242973+00:00
-- url     : https://prove2.me/theorems/61ec9323-779a-415b-8220-348476a20501
-- title:
--   Corrected clipped coherent-information capacity formula
-- statement:
--   Let $\rho_{AB}$ be a positive semidefinite density operator of trace one on two nonzero finite dimensional complex registers $A$ and $B$, whose dimensions may differ. Alice and Bob receive arbitrarily many independent copies of this one fixed state for free. Alice may send quantum systems to Bob through a noiseless channel; there is no free classical communication or feedback. Arbitrary local CPTP encodings, ancillas, disposal, and joint decoding are allowed. Entropies use logarithms to base two.
--
--   Write $C_{\rm sd}(\rho)$ for the operational supremum of classical bits per transmitted qubit: first choose integers $d\ge2$ and $n\ge1$; a block of $k$ channel uses sends a system of dimension $d^k$ and consumes $nk$ copies. For each error tolerance and rate slack, all sufficiently large positive $k$ admit encoders for all $m$-bit messages and one common decoder whose success is at least $1-\epsilon$ for every message. The normalized rate is $m/(k\log_2d)$, with vanishing error and arbitrarily small rate slack.
--
--   For every positive integer $n$ and every CPTP map $\Lambda:A^{\otimes n}\to A'$ with arbitrary positive finite output dimension, put $\sigma=(\Lambda\otimes\mathrm{id}_{B^{\otimes n}})(\rho^{\otimes n})$. Write $S_A(\sigma)=S(\sigma_{A'})$, $I_M(\sigma)=S(\sigma_{A'})+S(\sigma_{B^{\otimes n}})-S(\sigma)$, and $I^B(\sigma)=\max\{S(\sigma_{B^{\otimes n}})-S(\sigma),0\}$. Quotients below range only over outputs with $S_A(\sigma)>0$.
--
--   Let $\mathcal J(\rho)$ be the set of all corresponding positive-entropy quotients $I^B(\sigma)/S_A(\sigma)$, and let $\mathcal M(\rho)$ be the mutual-information quotient set above. Then
--
--   $$
--   C_{\rm sd}(\rho)=1+\sup\mathcal J(\rho)
--   =\max\{1,\sup\mathcal M(\rho)\},\qquad
--   \mathcal J(\rho)=\left\{\frac{I^B(\sigma)}{S_A(\sigma)}\right\}.
--   $$
--
--   The set $\mathcal J(\rho)$ is nonempty and contained in $[0,1]$. This reformulation displays the compression tradeoff between positive coherent information and the sender's entropy.
--
--   **Formalization Note** The denominator printed as $S(\rho_A)$ in Eq. (5) is corrected to the processed entropy $S(\Lambda(\rho_A^{\otimes n}))$, exactly as in Eq. (15). The equivalence holds after optimization and inclusion of baseline one; it is not a pointwise equality of clipped and signed quotients.
-- source:
--   Classical capacity of a noiseless quantum channel assisted by noisy entanglement, arXiv:quant-ph/0106080v3, PDF p. 3, Eq. (5), corrected by Eq. (15)

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P39

namespace QAlgorithms.Papers.Independent.Support50.P39

noncomputable section

open QAlgorithms

open Filter Topology

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arXiv:quant-ph/0106080v3, PDF p.3 Eq. (5), corrected using PDF p.7 Eq. (15),
and p.8. CORRECTION: S(rho_A) printed in Eq. (5) is replaced with the
entropy of Lambda(rho_A tensor n), as explicitly printed in Eq. (15).
For an entangled pure state, the printed denominator would give 1+n rather
than 2 under identity preprocessing. The mutual-information form agrees only
after optimization AND inclusion of baseline 1; no pointwise clipped identity
with mutual information is asserted for negative signed coherent information. -/
theorem clippedCoherentCapacity {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (hrho : IsDensityMatrix rho) :
    (coherentRatios rho).Nonempty ∧ BddAbove (coherentRatios rho) ∧
    (∀ r ∈ coherentRatios rho, 0 ≤ r ∧ r ≤ 1) ∧
    denseCodingCapacity rho = 1 + sSup (coherentRatios rho) ∧
    max 1 (sSup (mutualRatios rho)) = 1 + sSup (coherentRatios rho) := by sorry

end

end QAlgorithms.Papers.Independent.Support50.P39
