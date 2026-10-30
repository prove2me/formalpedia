-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P01_proposition14_inputAchievability
-- name    : QAlgorithms.Papers.Independent.Bridge50.P01.proposition14_inputAchievability
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T11:36:05.765217+00:00
-- url     : https://prove2.me/theorems/873728de-929e-481f-941c-924ecb1c048a
-- title:
--   Second-order EAC achievability for every pure resource
-- statement:
--   All Hilbert spaces are finite dimensional and nonzero. A channel is a completely positive trace-preserving map. Let $0<\varepsilon<1$. Write $L_n=\log_2 M_{\rm ea}^*(\mathcal N^{\otimes n},\varepsilon)$ for the optimal integer-message entanglement-assisted classical coding boundary with uniform messages and average error at most $\varepsilon$. Codes may act collectively and use arbitrary finite pure prior entanglement and local CPTP encoders, followed by a joint receiver POVM. There is no feedback. Let $C_{\rm ea}(\mathcal N)$ be the maximum output-reference quantum mutual information over pure input-reference states, and let $V_{\min}$ and $V_{\max}$ be the minimum and maximum mutual-information variances over all capacity-achieving resource states. All logarithms are base two. Put $V_\varepsilon=V_{\min}$ for $\varepsilon<1/2$ and $V_\varepsilon=V_{\max}$ for $\varepsilon\ge1/2$. The function $\Phi^{-1}$ is the inverse standard normal CDF.
--
--   For any pure density matrix $\psi_{AA'}$ with $A'\simeq A$, set $\omega=(\mathcal N\otimes{\rm id})(\psi)$. Let $I(A':B)_\omega=D(\omega\Vert\omega_{A'}\otimes\omega_B)$ and $V(A':B)_\omega=\operatorname{Tr}\omega[\log_2\omega-\log_2(\omega_{A'}\otimes\omega_B)-I(A':B)_\omega I]^2$. There is a sequence $K_n=O(\log n)$ such that for every positive integer $n$,
--
--   $$
--   L_n\ge nI(A':B)_\omega+\sqrt{nV(A':B)_\omega}\,\Phi^{-1}(\varepsilon)+K_n.
--   $$
--
--   The constants may depend on $\mathcal N,\varepsilon,\psi$ and are chosen before $n$. No capacity-achieving property of $\psi$ is assumed.
--
--   This input-wise result yields Theorem 3 by optimizing over resource states.
-- source:
--   On the Second-Order Asymptotics for Entanglement-Assisted Communication, arXiv:1405.1797v2, PDF p. 12, Proposition 14, (4.47)

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

/-- PDF pp.12–14, Proposition 14, Eq.(4.47): input-wise second-order bound;
the pure input need not achieve capacity, and is not a theorem hypothesis in
disguise. K is existential, with constants allowed to depend on this input. -/
theorem proposition14_inputAchievability
    {A B : Type} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    [DecidableEq A] [DecidableEq B] (N : Superop A B) (hN : IsChannel N)
    (epsilon : ℝ) (h0 : 0 < epsilon) (h1 : epsilon < 1) (psi : PureResource A) :
    ∃ K : ℕ → ℝ, IsLogRemainder K ∧ ∀ n : ℕ, 0 < n →
      (n : ℝ) * mutualInformation (resourceOutput N psi) +
        Real.sqrt ((n : ℝ) * mutualVariance (resourceOutput N psi)) * normalQuantile epsilon +
        K n ≤ codingBits (channelPower N n) epsilon := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P01

end
