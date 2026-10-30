-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P01_theorem3_achievability
-- name    : QAlgorithms.Papers.Independent.Bridge50.P01.theorem3_achievability
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T11:31:21.240507+00:00
-- url     : https://prove2.me/theorems/ee5ad0ac-1479-485b-8604-1253e2a325aa
-- title:
--   General-channel second-order EAC achievability
-- statement:
--   All Hilbert spaces are finite dimensional and nonzero. A channel is a completely positive trace-preserving map. Let $0<\varepsilon<1$. Write $L_n=\log_2 M_{\rm ea}^*(\mathcal N^{\otimes n},\varepsilon)$ for the optimal integer-message entanglement-assisted classical coding boundary with uniform messages and average error at most $\varepsilon$. Codes may act collectively and use arbitrary finite pure prior entanglement and local CPTP encoders, followed by a joint receiver POVM. There is no feedback. Let $C_{\rm ea}(\mathcal N)$ be the maximum output-reference quantum mutual information over pure input-reference states, and let $V_{\min}$ and $V_{\max}$ be the minimum and maximum mutual-information variances over all capacity-achieving resource states. All logarithms are base two. Put $V_\varepsilon=V_{\min}$ for $\varepsilon<1/2$ and $V_\varepsilon=V_{\max}$ for $\varepsilon\ge1/2$. The function $\Phi^{-1}$ is the inverse standard normal CDF.
--
--   For every fixed channel and error tolerance there exists a real sequence $K_n=O(\log n)$ such that, for all positive integers $n$,
--
--   $$
--   L_n\ge nC_{\rm ea}(\mathcal N)+\sqrt{nV_\varepsilon}\,\Phi^{-1}(\varepsilon)+K_n.
--   $$
--
--   Here $O(\log n)$ means that some $C>0$ and integer $n_0\ge2$, selected before $n$, satisfy $|K_n|\le C\log_2 n$ for all $n\ge n_0$. These constants may depend on the channel and $\varepsilon$.
--
--   This gives the general-channel direct part of the Gaussian approximation.
-- source:
--   On the Second-Order Asymptotics for Entanglement-Assisted Communication, arXiv:1405.1797v2, PDF p. 5, Theorem 3, (3.1)

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P01

noncomputable section

namespace QAlgorithms.Papers.Independent.Bridge50.P01

open QAlgorithms Filter MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

-- Reuse pinned accepted definitions; these are not other draft chunks.

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P58 (testingBeta testingD)

open QAlgorithms.Papers.Independent.Information100.P63 (normalCDF normalQuantile)

open QAlgorithms.Papers.Independent.Information100.P71 (channelPower)

open QAlgorithms.Papers.Independent.Information100.P80 (log2)

open QAlgorithms.Papers.Independent.Dependency50.P19 (mutualInformation)

open QAlgorithms.Papers.Independent.Dependency50.P24 (cqState)

open QAlgorithms.Papers.Independent.Dependency50.P36 (relativeEntropyFinite)

open QAlgorithms.Papers.Independent.Frontier30.P01 (classicalState)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.5–6, Theorem 3, Eq.(3.1): general-channel achievability; K is
existential, not a hypothesis. Constants may depend on N and epsilon. -/
theorem theorem3_achievability
    {A B : Type} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    [DecidableEq A] [DecidableEq B] (N : Superop A B) (hN : IsChannel N)
    (epsilon : ℝ) (h0 : 0 < epsilon) (h1 : epsilon < 1) :
    ∃ K : ℕ → ℝ, IsLogRemainder K ∧ ∀ n : ℕ, 0 < n →
      (n : ℝ) * eacSingleLetterCapacity N + Real.sqrt ((n : ℝ) * epsilonVariance N epsilon) *
        normalQuantile epsilon + K n ≤ codingBits (channelPower N n) epsilon := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P01

end
