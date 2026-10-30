-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P01_equation51_permutationConverse
-- name    : QAlgorithms.Papers.Independent.Bridge50.P01.equation51_permutationConverse
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T11:37:03.975623+00:00
-- url     : https://prove2.me/theorems/e658c949-c4f2-496b-9edb-65e7ebfc7391
-- title:
--   Permutation-restricted finite-block EAC converse
-- statement:
--   All Hilbert spaces are finite dimensional and nonzero. A channel is a completely positive trace-preserving map. Let $0<\varepsilon<1$. Write $L_n=\log_2 M_{\rm ea}^*(\mathcal N^{\otimes n},\varepsilon)$ for the optimal integer-message entanglement-assisted classical coding boundary with uniform messages and average error at most $\varepsilon$. Codes may act collectively and use arbitrary finite pure prior entanglement and local CPTP encoders, followed by a joint receiver POVM. There is no feedback. Let $C_{\rm ea}(\mathcal N)$ be the maximum output-reference quantum mutual information over pure input-reference states, and let $V_{\min}$ and $V_{\max}$ be the minimum and maximum mutual-information variances over all capacity-achieving resource states. All logarithms are base two. Put $V_\varepsilon=V_{\min}$ for $\varepsilon<1/2$ and $V_\varepsilon=V_{\max}$ for $\varepsilon\ge1/2$. The function $\Phi^{-1}$ is the inverse standard normal CDF.
--
--   For each positive integer $n$, let $\rho$ range over all permutation-invariant input densities on $A^{\otimes n}$, and let $\sigma$ range over all permutation-invariant densities on $B^{\otimes n}$. Choose the canonical purification $|\phi^\rho\rangle=\sum_{i,j}(\sqrt\rho)_{ij}|i\rangle|j\rangle$, and write $\rho_{A'^n}$ for its actual reference marginal. Then
--
--   $$
--   L_n\le\max_{\rho}\min_{\sigma}D_H^\varepsilon\!\left((\mathcal N^{\otimes n}\otimes{\rm id})(\phi^\rho)\,\middle\Vert\,\rho_{A'^n}\otimes\sigma\right).
--   $$
--
--   Both extrema are attained. The purification is invariant under simultaneous identical permutations of input and reference. Neither optimization is restricted to product states, and no covariance assumption is made on the channel.
--
--   This is the symmetry-restricted converse discussed in §5, rather than the conjectured general-channel Gaussian converse.
-- source:
--   On the Second-Order Asymptotics for Entanglement-Assisted Communication, arXiv:1405.1797v2, PDF p. 16, §5, (5.1)

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

/-- PDF p.16, Eq.(5.1): permutation-restricted max-min converse for arbitrary
channels. The first two conjuncts retain attainment of the printed min and
max, rather than silently weakening them to an infimum and supremum. -/
theorem equation51_permutationConverse
    {A B : Type} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    [DecidableEq A] [DecidableEq B] (N : Superop A B) (hN : IsChannel N)
    (n : ℕ) (hn : 0 < n) (epsilon : ℝ) (h0 : 0 < epsilon) (h1 : epsilon < 1) :
    (∀ rho ∈ symmetricDensities A n,
      IsLeast (converseAlternatives N n epsilon rho)
        (sInf (converseAlternatives N n epsilon rho))) ∧
    IsGreatest (converseInputValues N n epsilon) (sSup (converseInputValues N n epsilon)) ∧
    (codingBits (channelPower N n) epsilon : EReal) ≤
      sSup (converseInputValues N n epsilon) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P01

end
