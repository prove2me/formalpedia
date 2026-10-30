-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P35_positiveErrorLimit
-- name    : QAlgorithms.Papers.Independent.Bridge50.P35.positiveErrorLimit
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:13:34.055282+00:00
-- url     : https://prove2.me/theorems/1b3c64c8-552b-48ee-bf00-93d61be22b45
-- title:
--   Theorem 2: asymptotic consequence with corrected positive tolerances
-- statement:
--   Let $W:x\mapsto\rho_x^{BE}$ be a degraded memoryless cqq wiretap channel on a finite nonempty input alphabet and finite positive-dimensional output spaces. Use unassisted stochastic encoding, a uniform message, a Bob POVM, and the two separate purified-distance error criteria: transmission against the uniform perfectly correlated classical state, and secrecy against a product with one optimized normalized Eve state. Let $M_W(n,\epsilon,\delta)$ be the largest admissible message count and let $P(W)$ be the operational capacity with both errors vanishing. All rates are in bits.
--
--   For fixed strictly positive $\epsilon,\delta$ with $\epsilon+2\delta<1$,
--   $$
--   \lim_{n\to\infty}\frac{\log_2 M_W(n,\epsilon,\delta)}{n}=P(W).
--   $$
--   This gives the asymptotic consequence of the finite-block converse together with operational achievability, on the corrected domain of positive fixed tolerances.
--
--   **Source Correction** The printed hypotheses permit zero tolerances. Both tolerances are required to be strictly positive here. A full-support binary symmetric Bob channel with a constant Eve has positive private capacity but permits only one exactly decodable message at every blocklength. The original endpoint assertion is separately deferred, and this correction requires independent moderation.
--
--   **Formalization Note** The limit uses extended-real rates, which are finite for these tolerances. The unused zero-blocklength rate is explicitly set to zero.
-- source:
--   "Pretty strong" converse for the private capacity of degraded quantum wiretap channels, arXiv:1601.06611v2, PDF p. 2, Theorem 2, asymptotic consequence with corrected positive tolerances

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P35

noncomputable section

namespace QAlgorithms.Papers.Independent.Bridge50.P35

open scoped BigOperators Matrix ComplexConjugate

open Filter

open QAlgorithms.Papers.Independent.Dependency50.P48 (cqPower)

open QAlgorithms.Papers.Independent.Information100.P56 (PrivateCode)

open QAlgorithms.Papers.Independent.Information100.P67
  (purifiedDistance idealClassicalKey)

attribute [local instance] Classical.propDecidable

variable {X B E : Type*}

variable [Fintype X] [DecidableEq X]

variable [Fintype B] [DecidableEq B]

variable [Fintype E] [DecidableEq E]

/-- Corrected positive-tolerance consequence of Theorem 2, PDF p.2.
PRINTED: epsilon,delta≥0 with epsilon+2delta<1. CHANGED: epsilon,delta>0.
WHY: a full-support binary symmetric Bob channel with constant Eve has
positive capacity but exact-decoding message number one at every length.
Both strict inequalities are retained: vanishing secrecy does not imply
exact secrecy. The original printed endpoint assertion is deferred in HARD.md;
this correction requires independent moderation. -/
theorem positiveErrorLimit [Nonempty X] [Nonempty B] [Nonempty E]
    (W : CqqChannel X B E) (hW : W.IsDegraded)
    (epsilon delta : ℝ) (he : 0 < epsilon) (hd : 0 < delta)
    (hslack : epsilon + 2 * delta < 1) :
    Tendsto (fun n : ℕ => cqqBlockRate W n epsilon delta) atTop
      (nhds (cqqPrivateCapacity W)) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P35

end
