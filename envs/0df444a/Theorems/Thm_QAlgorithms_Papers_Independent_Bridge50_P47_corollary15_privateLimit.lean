-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P47_corollary15_privateLimit
-- name    : QAlgorithms.Papers.Independent.Bridge50.P47.corollary15_privateLimit
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T08:49:05.080993+00:00
-- url     : https://prove2.me/theorems/0c042a3f-3bb9-43d0-bb3c-81de5208c822
-- title:
--   Corollary 15: fixed-error private capacity limit
-- statement:
--   Let $\mathcal N$ be a degradable channel on nonzero finite quantum systems. Use uniform messages, arbitrary mixed signal states, POVM decoding, purified error of the $X\widehat X$ marginal, and separately optimized purified privacy of the $XE$ marginal. Let $P(\mathcal N)$ be the operational private capacity obtained by taking vanishing positive error and privacy tolerances. For any fixed $\varepsilon,\delta>0$ satisfying $\varepsilon+2\delta<1/\sqrt2$, the limit exists and
--
--   $$
--   \lim_{n\to\infty}\frac{\log_2 M(n,\varepsilon,\delta)}n=P(\mathcal N).
--   $$
--
--   The same positive error and privacy tolerances may be kept at every blocklength. Achievability and the degradable-channel capacity identities are conclusions available from the cited background, not extra premises.
-- source:
--   "Pretty strong" converse for the quantum capacity of degradable channels, arXiv:1301.4927v3, PDF p. 9, Corollary 15: fixed-error private capacity limit

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P47

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Bridge50.P47

open QAlgorithms.Papers.Independent.Information100

variable {A B E F R I O : Type*}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype E] [DecidableEq E] [Fintype F] [DecidableEq F]

variable [Fintype R] [DecidableEq R] [Fintype I] [DecidableEq I]

variable [Fintype O] [DecidableEq O]

/-- Corollary 15, PDF p.9: convergence to the operational private capacity,
with both fixed tolerances strictly positive and the asymmetric combined threshold.
The imported uniform joint-infidelity capacity is used only in the vanishing-error
limit: joint convergence implies both marginal criteria by contractivity, and
vanishing separate criteria imply joint convergence by the trace-distance triangle
inequality. The finite-block logM retains this paper's two separate criteria. -/
theorem corollary15_privateLimit [Nonempty A] [Nonempty B] [Nonempty E]
    (U : Matrix (B × E) A ℂ) (hU : P67.IsDegradable U)
    (epsilon delta : ℝ) (he : 0 < epsilon) (hd : 0 < delta)
    (hsmall : epsilon + 2 * delta < 1 / Real.sqrt 2) :
    Tendsto (fun n : ℕ => logM U n epsilon delta / (n : ℝ)) atTop
      (nhds (P67.privateCapacity .uniformOptimized U)) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P47

end
