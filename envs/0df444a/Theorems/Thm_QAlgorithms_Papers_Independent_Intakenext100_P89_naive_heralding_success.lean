-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P89_naive_heralding_success
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P89.naive_heralding_success
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:28:29.565787+00:00
-- url     : https://prove2.me/theorems/c6597fc1-1662-4e55-abdc-ffaaf64a91ef
-- title:
--   Naive multiplexing: heralding recursion and corrected final success
-- statement:
--   Assume only independent photon loss. The source, detector and chip-to-fiber efficiencies $\eta_s,\eta_d,\eta_c$ lie in $(0,1]$; fiber attenuation $\alpha$ is positive, chip attenuation $\beta$ is nonnegative, feedforward delays $\tau_s,\tau_f$ are nonnegative and propagation speeds $c_{\rm ch},c_f$ are positive, in consistent units. Put $v=\eta_s\eta_d$, $h=v/(2-v)$, and $a=e^{-\beta\tau_s c_{\rm ch}}$. Let $k\ge0$ and let the numbers of major nodes $n$, channels per direction $m$, and multiplexing counts $g=n_{\rm GHZ},b=n_B,t=n_{\rm meas}$ be positive integers. Define $G=[v(2-v)]^3/32$, $Q_l=(ha^l)^2/2$, and $P'=(ha^{k+1})^{4m+1}$. In the actual independent-attempt naive experiment, let $P_l$ denote the probability of heralding a level-$l$ cluster, $P_{c1}$ that of a final measured cluster at one major node, and $P_{cn}$ that of final clusters at all $n$ nodes. Then
--
--   $$\begin{aligned}P_0&=1-(1-G)^g,\\P_{l+1}&=1-(1-P_l^2Q_{l+1})^b\quad(l\ge0),\\P_{c1}&=1-(1-P_kP')^t,\\P_{cn}&=P_{c1}^{\,n}.\end{aligned}$$
--
--   These probabilities are finite event sums, with independent copies selected at each multiplexing stage. They retain the probability of constructing both daughters, rather than only the final conditional fusion success.
--
--   **Source correction.** Page 8 prints $P_{c1}=1-(Q_kP')^t$. The corrected formula above follows the stated complete-attempt construction and has the proper zero- and unit-success endpoints. Independent moderation of this correction is pending.
-- source:
--   Rate-distance tradeoff and resource costs for all-optical quantum repeaters, arXiv:1603.01353v4, PDF p. 7, III.A.1: recursive naive heralding success, with documented correction

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P89

namespace QAlgorithms.Papers.Independent.Intakenext100.P89

open scoped BigOperators ComplexConjugate

-- Accepted probability primitives: symbol true is success; choose n x is zero for x > n.

open QAlgorithms.Papers.Independent.Information100.P54 (binomialMass)

open QAlgorithms.Papers.Independent.Information100.P56 (bernoulli)

noncomputable section

/-- Source pp.7--8, III.A.1: recursive, final and network preparation probabilities.
CORRECTION: p.8 prints Pc1 = 1-(Qk P')^nmeas. The actual experiment requires
Pc1 = 1-(1-Pk P')^nmeas: Qk is only conditional fusion success and the printed formula
reverses the zero/one success endpoints. Independent moderation is required. -/
theorem naive_heralding_success (d : Devices) (k m n nGHZ nB nMeas : ℕ)
    (hm : 0 < m) (hn : 0 < n) (hGHZ : 0 < nGHZ) (hB : 0 < nB)
    (hMeas : 0 < nMeas) :
    naiveClusterLaw d nGHZ nB 0 true = 1 - (1 - ghzSuccess d) ^ nGHZ ∧
    (∀ l : ℕ, naiveClusterLaw d nGHZ nB (l + 1) true =
      1 - (1 - (naiveClusterLaw d nGHZ nB l true) ^ 2 *
        naiveFusionSuccess d (l + 1)) ^ nB) ∧
    naiveFinalLaw d k m nGHZ nB nMeas true =
      1 - (1 - naiveClusterLaw d nGHZ nB k true *
        finalMeasurementSuccess d k m) ^ nMeas ∧
    allLaw n (naiveFinalLaw d k m nGHZ nB nMeas) true =
      (naiveFinalLaw d k m nGHZ nB nMeas true) ^ n := by sorry

end

end QAlgorithms.Papers.Independent.Intakenext100.P89
