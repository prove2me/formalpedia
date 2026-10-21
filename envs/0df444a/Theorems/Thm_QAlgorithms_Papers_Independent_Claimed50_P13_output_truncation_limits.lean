-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P13_output_truncation_limits
-- name    : QAlgorithms.Papers.Independent.Claimed50.P13.output_truncation_limits
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:42:41.949776+00:00
-- url     : https://prove2.me/theorems/4135fcea-09f6-40d6-ac67-c9601b6854bb
-- title:
--   Section 6 explicit supporting limits (41) and (42)
-- statement:
--   All systems are nonzero separable complex Hilbert spaces. States are positive trace-class operators of trace one, channels are complex-linear completely positive trace-preserving maps on the full trace class, and all logarithms are natural. Write $H$ for von Neumann entropy, $I(\rho,\Phi)$ for the relative-entropy mutual information of a purified input, and $C_\chi$, $C$, $C_{\rm ea}$ for the single-use Holevo, regularized classical and assisted classical capacities, respectively. A second argument $\rho$ in $C_\chi(\Phi,\rho)$ fixes the exact input average. Let $\widehat\Phi$ be complementary to $\Phi$, obtained by the other partial trace of the same Stinespring isometry. Fix the common Stinespring isometry $V$, an input state $\rho$ with finite entropy, and a pure-state ensemble $\mu$ with barycenter $\rho$. Let $P_n$ be increasing finite-rank orthogonal output projections tending strongly to the identity. Define $\Phi_n(X)=P_n\Phi(X)P_n$ and $\widehat\Phi_n(X)=\operatorname{Tr}_B[(P_n\otimes I)VXV^*(P_n\otimes I)]$. Then
--
--   $$I(\rho,\Phi_n)\to I(\rho,\Phi),\qquad\chi_{\Phi_n}(\mu)\to\chi_\Phi(\mu),\qquad\chi_{\widehat\Phi_n}(\mu)\to\chi_{\widehat\Phi}(\mu).$$
--
--   These limits justify output truncation of the information quantities without replacing compression by an erasure channel.
-- source:
--   On the entanglement-assisted classical capacity of infinite-dimensional quantum channels, arXiv:1210.6926v2, PDF p. 21, Section 6 explicit supporting limits (41) and (42)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P13

noncomputable section

open MeasureTheory Filter

open scoped ENNReal NNReal Topology BigOperators

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

namespace QAlgorithms.Papers.Independent.Claimed50.P13

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Supporting limits (41)--(42), PDF pp.21--23: all THREE limits, with
a trace-decreasing compression and its complement from the SAME isometry. -/
theorem output_truncation_limits {I J K : Type}
    [Countable I] [Countable J] [Countable K] [Nonempty I] [Nonempty J] [Nonempty K]
    (Phi : MI.Channel I J) (Psi : MI.Channel I K)
    (V : Hilbert I →ₗᵢ[ℂ] Hilbert (J × K))
    (hV : ∀ rho : State I,
      Phi.val rho.coefficients = MI.traceSecond (MI.boundedConjugation V.toContinuousLinearMap rho.coefficients) ∧
      Psi.val rho.coefficients = MI.traceFirst (MI.boundedConjugation V.toContinuousLinearMap rho.coefficients))
    (P : ExhaustingProjections J) (rho : State I)
    (hfinite : MI.homogeneousEntropy rho.coefficients < ⊤)
    (mu : Ens.GeneralizedEnsemble I) (haverage : Ens.HasAverage mu rho)
    (hpure : ∀ᵐ sigma ∂(mu : Measure (State I)), sigma ∈ Ens.pureStates I) :
    Tendsto (fun n => MI.mutualInformation rho.coefficients (compressedAction Phi.val (P.proj n)))
      atTop (𝓝 (MI.mutualInformation rho.coefficients Phi.val)) ∧
    Tendsto (fun n => Ens.ensembleHolevo (compressedAction Phi.val (P.proj n)) mu)
      atTop (𝓝 (Ens.ensembleHolevo Phi.val mu)) ∧
    Tendsto (fun n => Ens.ensembleHolevo (compressedComplement V (P.proj n)) mu)
      atTop (𝓝 (Ens.ensembleHolevo Psi.val mu)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P13

end
