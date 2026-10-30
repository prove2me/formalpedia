-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P01_covariant_gaussian
-- name    : QAlgorithms.Papers.Independent.Bridge50.P01.covariant_gaussian
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T11:30:23.011063+00:00
-- url     : https://prove2.me/theorems/6e1ce2ae-47d2-431b-be2d-59f55798c7ad
-- title:
--   Gaussian approximation and dispersion for irreducibly input-covariant channels
-- statement:
--   All Hilbert spaces are finite dimensional and nonzero. A channel is a completely positive trace-preserving map. Let $0<\varepsilon<1$. Write $L_n=\log_2 M_{\rm ea}^*(\mathcal N^{\otimes n},\varepsilon)$ for the optimal integer-message entanglement-assisted classical coding boundary with uniform messages and average error at most $\varepsilon$. Codes may act collectively and use arbitrary finite pure prior entanglement and local CPTP encoders, followed by a joint receiver POVM. There is no feedback. Let $C_{\rm ea}(\mathcal N)$ be the maximum output-reference quantum mutual information over pure input-reference states, and let $V_{\min}$ and $V_{\max}$ be the minimum and maximum mutual-information variances over all capacity-achieving resource states. All logarithms are base two. Put $V_\varepsilon=V_{\min}$ for $\varepsilon<1/2$ and $V_\varepsilon=V_{\max}$ for $\varepsilon\ge1/2$. The function $\Phi^{-1}$ is the inverse standard normal CDF.
--
--   Suppose a compact group has continuous projective unitary representations $U$ on the input and $V$ on the output such that $\mathcal N(U(g)\rho U(g)^\dagger)=V(g)\mathcal N(\rho)V(g)^\dagger$ for every group element and input density matrix. Assume the input representation is irreducible. Let $\Phi_{AA'}$ be the maximally entangled input state and $\omega=(\mathcal N\otimes{\rm id})(\Phi_{AA'})$. Then
--
--   $$
--   C_{\rm ea}(\mathcal N)=I(A':B)_\omega,\qquad V_{\min}=V_{\max}=V(A':B)_\omega,
--   $$
--
--   and there is a real sequence $K_n=O(\log n)$ such that, for every positive integer $n$,
--
--   $$
--   L_n=nC_{\rm ea}(\mathcal N)+\sqrt{nV_\varepsilon}\,\Phi^{-1}(\varepsilon)+K_n.
--   $$
--
--   If $\varepsilon\ne1/2$, the operational dispersion $\limsup_{n\to\infty}n^{-1}[(L_n-nC_{\rm ea})/\Phi^{-1}(\varepsilon)]^2$ equals $V(A':B)_\omega$.
--
--   This characterizes the second-order convergence for this class of channels; it imposes neither output irreducibility nor equality of input and output dimensions.
-- source:
--   On the Second-Order Asymptotics for Entanglement-Assisted Communication, arXiv:1405.1797v2, PDF p. 14, §4.4; (4.79)–(4.82)

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

/-- PDF pp.14–16, §4.4 and Eqs.(4.79)–(4.82): Gaussian approximation and
operational dispersion for compact-group covariant channels with irreducible
input representation. Output dimension and representation are unrestricted.
Capacity and optimizer variances are defined independently of this input. -/
theorem covariant_gaussian
    {A B G : Type} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    [DecidableEq A] [DecidableEq B] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (N : Superop A B) (hN : IsChannel N)
    (U : G → Matrix.unitaryGroup A ℂ) (V : G → Matrix.unitaryGroup B ℂ)
    (hU : IsProjectiveRepresentation U) (hV : IsProjectiveRepresentation V)
    (hIrreducible : InputActionIrreducible U) (hCovariant : IsInputOutputCovariant N U V)
    (epsilon : ℝ) (h0 : 0 < epsilon) (h1 : epsilon < 1) :
    let omega := tensorIdentity N (pureDensity (finiteMaxEntangled A))
    eacSingleLetterCapacity N = mutualInformation omega ∧
    varianceMin N = mutualVariance omega ∧
    varianceMax N = mutualVariance omega ∧
    (∃ K : ℕ → ℝ, IsLogRemainder K ∧ ∀ n : ℕ, 0 < n →
      codingBits (channelPower N n) epsilon = (n : ℝ) * eacSingleLetterCapacity N +
        Real.sqrt ((n : ℝ) * epsilonVariance N epsilon) * normalQuantile epsilon + K n) ∧
    (epsilon ≠ 1 / 2 → eaOperationalDispersion N epsilon = (mutualVariance omega : EReal)) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P01

end
