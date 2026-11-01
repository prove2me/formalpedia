-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P10_assistance_rate_vanishes
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P10.assistance_rate_vanishes
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:38:33.918862+00:00
-- url     : https://prove2.me/theorems/88f4d165-4f05-418d-bf0e-e60d06fea7dc
-- title:
--   Secret-key consumption has vanishing rate
-- statement:
--   Under the degraded binary cq wiretap-channel and commuting Eve-output assumptions, fix $0<\beta<1/2$ and use $N=2^n$. Let $\mathcal P_N$ be Eve's strict poor set, and let $\mathcal B_N(W,\beta)$ be Bob's bad set. Define $\mathcal X_N=\mathcal P_N(W^*,\beta)^{\mathrm c}\cap\mathcal B_N(W,\beta)$. Then
--
--   $$
--   \lim_{n\to\infty}\frac{|\mathcal X_{2^n}|}{2^n}=0.
--   $$
--
--   These indices carry independent uniform preshared secret bits in the wiretap scheme. The conclusion allows nonzero, growing sublinear key length; the same index count is the ebit-consumption rate in the coherent construction.
-- source:
--   Polar codes for degradable quantum channels, arXiv:1109.5346v3, PDF p. 6, Proposition 7: vanishing secret-key rate

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P10

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P10

open scoped BigOperators Matrix ComplexConjugate

open Filter

-- Accepted definitions, without paper-local aliases.

open QAlgorithms.Papers.Independent.Information100.P58 (basisDensity)

open QAlgorithms.Papers.Independent.Information100.P67 (squaredFidelity)

open QAlgorithms.Papers.Independent.Claimed50.P48 (indexedKrausDilation)

/-- PDF p.6, Proposition 7: vanishing secret-key rate, allowing nonzero sublinear
key length at every finite blocklength. -/
theorem assistance_rate_vanishes {B E : Type*} [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype E] [DecidableEq E] [Nonempty E]
    (V : Wiretap B E) (beta : ℝ) (hpos : 0 < beta) (hbeta : beta < 1 / 2) :
    Tendsto (fun n => leafProbability (assistanceSet V n beta)) atTop (nhds 0) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P10

end
