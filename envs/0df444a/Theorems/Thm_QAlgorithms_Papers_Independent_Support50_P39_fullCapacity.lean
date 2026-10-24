-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P39_fullCapacity
-- name    : QAlgorithms.Papers.Independent.Support50.P39.fullCapacity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T21:57:53.795768+00:00
-- url     : https://prove2.me/theorems/588fb195-7433-475f-bf1e-21f6f0910133
-- title:
--   Full noisy-entanglement-assisted capacity with the unassisted baseline
-- statement:
--   Let $\rho_{AB}$ be a positive semidefinite density operator of trace one on two nonzero finite dimensional complex registers $A$ and $B$, whose dimensions may differ. Alice and Bob receive arbitrarily many independent copies of this one fixed state for free. Alice may send quantum systems to Bob through a noiseless channel; there is no free classical communication or feedback. Arbitrary local CPTP encodings, ancillas, disposal, and joint decoding are allowed. Entropies use logarithms to base two.
--
--   Write $C_{\rm sd}(\rho)$ for the operational supremum of classical bits per transmitted qubit: first choose integers $d\ge2$ and $n\ge1$; a block of $k$ channel uses sends a system of dimension $d^k$ and consumes $nk$ copies. For each error tolerance and rate slack, all sufficiently large positive $k$ admit encoders for all $m$-bit messages and one common decoder whose success is at least $1-\epsilon$ for every message. The normalized rate is $m/(k\log_2d)$, with vanishing error and arbitrarily small rate slack.
--
--   For every positive integer $n$ and every CPTP map $\Lambda:A^{\otimes n}\to A'$ with arbitrary positive finite output dimension, put $\sigma=(\Lambda\otimes\mathrm{id}_{B^{\otimes n}})(\rho^{\otimes n})$. Write $S_A(\sigma)=S(\sigma_{A'})$, $I_M(\sigma)=S(\sigma_{A'})+S(\sigma_{B^{\otimes n}})-S(\sigma)$, and $I^B(\sigma)=\max\{S(\sigma_{B^{\otimes n}})-S(\sigma),0\}$. Quotients below range only over outputs with $S_A(\sigma)>0$.
--
--   Let $\mathcal M(\rho)$ be the set of all these positive-entropy mutual-information quotients. Then
--
--   $$
--   C_{\rm sd}(\rho)=\max\left\{1,\sup\mathcal M(\rho)\right\},\qquad
--   \mathcal M(\rho)=\left\{\frac{I_M(\sigma)}{S_A(\sigma)}\right\},\qquad
--   1\le C_{\rm sd}(\rho)\le2.
--   $$
--
--   The set $\mathcal M(\rho)$ is nonempty and lies in $[0,2]$, and the operational rate set is nonempty and bounded above. Every nonnegative rate strictly below the displayed value is achievable with some fixed finite $d,n$ chosen before the error and rate-slack limits. Conversely, for any fixed $d\ge2,n\ge1$, every family of worst-message block codes with errors tending to zero has normalized rate eventually at most $\max\{1,\sup\mathcal M(\rho)\}+\delta$ for each $\delta>0$, even when its rates do not converge.
--
--   This is an operational capacity identity with finite near-optimal protocols; no maximizing block length or output dimension is required.
--
--   **Formalization Note** This is an explicit source correction. The baseline and exclusion of zero denominators repair Eqs. (3),(4) using the unassisted strategy and the compression argument in Eqs. (13),(15).
-- source:
--   Classical capacity of a noiseless quantum channel assisted by noisy entanglement, arXiv:quant-ph/0106080v3, PDF p. 2, Eqs. (3),(4),(6),(15); abstract

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P39

namespace QAlgorithms.Papers.Independent.Support50.P39

noncomputable section

open QAlgorithms

open Filter Topology

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arXiv:quant-ph/0106080v3, PDF pp.1--3,6--8, Eqs. (3),(4),(6),(15).
Full operational noisy-entanglement-assisted capacity, with achievability below
the supremum and a converse for every reliable fixed-(d,n) block family.
CORRECTION: the printed Eq. (3) omits the unassisted baseline 1, and Eq. (4)
is undefined at S(A)=0. We optimize only positive-entropy quotients and take
max with 1. Product resources have ratio 0 and operational capacity 1.
No global optimizer in n or output dimension is asserted or assumed. -/
theorem fullCapacity {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (hrho : IsDensityMatrix rho) :
    (mutualRatios rho).Nonempty ∧ BddAbove (mutualRatios rho) ∧
    (∀ r ∈ mutualRatios rho, 0 ≤ r ∧ r ≤ 2) ∧
    (operationalRates rho).Nonempty ∧ BddAbove (operationalRates rho) ∧
    denseCodingCapacity rho = max 1 (sSup (mutualRatios rho)) ∧
    1 ≤ denseCodingCapacity rho ∧ denseCodingCapacity rho ≤ 2 ∧
    (∀ R : ℝ, 0 ≤ R → R < max 1 (sSup (mutualRatios rho)) →
      ∃ d n : ℕ, 2 ≤ d ∧ 0 < n ∧ FixedRate rho d n R) ∧
    (∀ d n : ℕ, 2 ≤ d → 0 < n →
      ∀ (m : ℕ → ℕ) (epsilon : ℕ → ℝ), ReliableFamily rho d n m epsilon →
      ∀ delta : ℝ, 0 < delta → ∃ K : ℕ, ∀ k : ℕ, K ≤ k → 0 < k →
        (m k : ℝ) / ((k : ℝ)*Real.logb 2 d) ≤
          max 1 (sSup (mutualRatios rho)) + delta) := by sorry

end

end QAlgorithms.Papers.Independent.Support50.P39
