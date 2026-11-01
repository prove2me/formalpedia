-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P10_wiretap_rate
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P10.wiretap_rate
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:37:41.006206+00:00
-- url     : https://prove2.me/theorems/cf682ad0-c879-44dc-85cf-89fe0238e71a
-- title:
--   Information-set rate tends to symmetric private information
-- statement:
--   Let $x\mapsto\rho_x^{BE}$ be a binary cq wiretap channel with finite nonempty registers. Its Bob and Eve marginals are $W$ and $W^*$, one CPTP map degrades $W$ to $W^*$ for both letters, and the two Eve letter states commute. Fix $0<\beta<1/2$. At each $N=2^n$, use the prescribed fidelity-defined sets and put $\mathcal A_N=\mathcal P_N(W^*,\beta)\cap\mathcal G_N(W,\beta)$. The polar construction places its information bits on these indices, so its information rate satisfies
--
--   $$
--   \lim_{n\to\infty}\frac{|\mathcal A_{2^n}|}{2^n}=I(W)-I(W^*).
--   $$
--
--   This is the rate of the specified index-set construction. The separate preshared-key consumption is not subtracted, and no unrestricted private-capacity optimization is asserted.
-- source:
--   Polar codes for degradable quantum channels, arXiv:1109.5346v3, PDF p. 5, Theorem 5: quantum wiretap polar-code rate

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P10

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P10

open scoped BigOperators Matrix ComplexConjugate

open Filter

-- Accepted definitions, without paper-local aliases.

open QAlgorithms.Papers.Independent.Information100.P58 (basisDensity)

open QAlgorithms.Papers.Independent.Information100.P67 (squaredFidelity)

open QAlgorithms.Papers.Independent.Claimed50.P48 (indexedKrausDilation)

/-- PDF pp.5–6, Theorem 5: prescribed information-set rate along N=2^n.
This is |A|/N without subtracting the separate secret-key consumption. -/
theorem wiretap_rate {B E : Type*} [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype E] [DecidableEq E] [Nonempty E]
    (V : Wiretap B E) (beta : ℝ) (hpos : 0 < beta) (hbeta : beta < 1 / 2) :
    Tendsto (fun n => leafProbability (informationSet V n beta)) atTop
      (nhds (symmetricInformation V.bob - symmetricInformation V.eve)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P10

end
