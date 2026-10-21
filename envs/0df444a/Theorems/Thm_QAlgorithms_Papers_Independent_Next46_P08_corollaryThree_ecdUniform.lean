-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P08_corollaryThree_ecdUniform
-- name    : QAlgorithms.Papers.Independent.Next46.P08.corollaryThree_ecdUniform
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T13:58:04.993663+00:00
-- url     : https://prove2.me/theorems/28caad9e-62c2-453f-8af7-10224c96384a
-- title:
--   Corrected Corollary 3 A–B: uniform continuity of all three constrained capacities
-- statement:
--   Let $A,B$ be infinite-dimensional separable complex systems with positive densely defined self-adjoint Hamiltonians $H_A,H_B$. Fix $E\ge E_0^A$ and an ECD input level $L>E_0^A$. The distance $D_L$ is the actual normalized-input, reference-amplified trace-norm supremum at input energy $L$. Let $C_\chi,C,C_{\rm ea}$ be respectively the constrained Holevo capacity over finite/countable barycenter-constrained ensembles, its all-block regularization, and the constrained supremum of genuine purification-based channel mutual information, all in nats.
--
--   1. If $H_A$ has discrete finite-multiplicity spectrum tending to infinity and $\operatorname{Tr}e^{-\beta H_B}<\infty$ for every $\beta>0$, then for each common finite $k\ge0$ all three capacities are finite and uniformly continuous for $D_L$ on
--
--   $$
--   \mathcal K_{E,k}=\{\Phi:\operatorname{Tr}H_B\Phi(\rho)\le kE\text{ for every state }\rho\text{ with }\operatorname{Tr}H_A\rho\le E\}.
--   $$
--
--   2. If only the input Hamiltonian satisfies $\operatorname{Tr}e^{-\beta H_A}<\infty$ for every $\beta>0$, then $C_{\rm ea}$ is finite and uniformly continuous for $D_L$ on the set of all channels, with no output Gibbs or energy-amplification assumption.
--
--   In each case uniform continuity means, for each indicated capacity $V$ and channel set $\mathcal S$,
--
--   $$
--   \forall\eta>0\ \exists\delta>0\ \forall\Phi,\Psi\in\mathcal S,\quad
--   D_L(\Phi,\Psi)<\delta\ \Longrightarrow\ |V(\Phi)-V(\Psi)|<\eta.
--   $$
--
--   The modulus is uniform over the channels, and the amplification condition is at the single fixed input energy $E$. This explicitly corrects the source's every-compatible-metric wording to the specified ECD uniformity; it does not resolve the separately deferred literal claim.
-- source:
--   Energy-constrained diamond norms and their use in quantum information theory, arXiv:1706.00361v2, PDF p. 18, Corollary 3 A–B: explicitly corrected ECD-uniform content

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P08

noncomputable section

open Filter MeasureTheory

open scoped Topology ENNReal NNReal BigOperators

namespace QAlgorithms.Papers.Independent.Next46.P08

export QAlgorithms.Papers.Independent.Claimed50.P32 (StrongChannel)

export QAlgorithms.Papers.Independent.Frontier18.P07
  (GeneralizedEnsemble ensembleHolevo)

export QAlgorithms.Papers.Independent.Claimed50.P39 (g)

/-- Corollary 3 A–B, PDF p.18, corrected to the specified ECD uniformity.
Printed: every compatible metric, through footnote 11 and Remark 4.
Changed: every fixed input ECD level L>ground. Reason: equality of topologies
alone does not identify uniformities. A quantifies a common finite k before
all channels and includes all three capacities. B imposes only input Gibbs;
its conclusion concerns ALL channels and imposes no output-energy condition. -/
theorem corollaryThree_ecdUniform (HA HB : Forms.PositiveObservable ℕ)
    (E : ℝ) (hE : formGroundEnergy HA ≤ E)
    (L : ℝ) (hL : formGroundEnergy HA < L) :
    (DiscreteSpectrum HA →
      QAlgorithms.Papers.Independent.Claimed50.P13.GibbsCondition HB →
      ∀ k : ℝ, 0 ≤ k →
        CapacityUniformOn HA L (constrainedChi HA E)
          {Phi | FixedEnergyAmplification HA HB E k Phi} ∧
        CapacityUniformOn HA L (constrainedClassical HA E)
          {Phi | FixedEnergyAmplification HA HB E k Phi} ∧
        CapacityUniformOn HA L (constrainedAssisted HA E)
          {Phi | FixedEnergyAmplification HA HB E k Phi}) ∧
    (QAlgorithms.Papers.Independent.Claimed50.P13.GibbsCondition HA →
      CapacityUniformOn HA L (constrainedAssisted HA E) Set.univ) := by sorry

end QAlgorithms.Papers.Independent.Next46.P08

end
