-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P18_output_mutual_information_continuity
-- name    : QAlgorithms.Papers.Independent.Support50.P18.output_mutual_information_continuity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T20:26:24.847952+00:00
-- url     : https://prove2.me/theorems/e945ee84-0450-4735-bf06-ba731d6cfdc4
-- title:
--   Proposition 5: channel-independent output mutual-information bound
-- statement:
--   Let $\Phi:A\to B$ be any CPTP channel on trace class and $R$ any separable reference. Suppose $H_A\ge0$ satisfies (22), write $E_0$ for its ground infimum, and fix finite $E\ge E_0$. Put $J_\Phi(\rho)=I(B:R)_{(\Phi\otimes\mathrm{Id}_R)(\rho)}$, with mutual information defined by extended relative entropy. This function is finite and uniformly continuous in trace distance on states of $AR$ with input $A$ energy at most $E$. The entropy capacity is finite at every finite budget above $E_0$, and
--
--   $$|J_\Phi(\rho)-J_\Phi(\sigma)|\le2\sqrt{2\varepsilon}\,F_{H_A}(E/\varepsilon)+2g(\sqrt{2\varepsilon})$$
--
--   whenever both input energies are at most $E$ and $0<\varepsilon\le1/2$ bounds their half trace distance. For pure joint inputs the modulus parameter may be replaced by $\varepsilon^2/2$ under the original distance hypothesis. The bound is independent of the channel and places no energy constraint on its output.
-- source:
--   Adaptation of the Alicki-Fannes-Winter method for the set of states with bounded energy and its use, arXiv:1609.07044v5, PDF p. 17, Proposition 5

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P18

noncomputable section

open Filter

open scoped ENNReal NNReal BigOperators Topology

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Support50.P18

open QAlgorithms.Papers.Independent.Dependency50.P33 (State PureState traceSize rankOne)

open QAlgorithms.Papers.Independent.Frontier18.P01 (convexOperatorMixture traceSecond)

open QAlgorithms.Papers.Independent.Frontier18.P07
  (extendedEntropyNats extendedRelativeEntropyNats)

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

open QAlgorithms.Papers.Independent.Renew46.P08
  (coefficientEnergy entropySupremum extendedHalfTraceDistance)

/-- Proposition 5, PDF pp.16--17, (48): arbitrary CPTP channel and reference.
Condition (22) forces discrete spectrum (Appendix p.21), justifying the choice
of an energy eigenbasis on A without a new spectral hypothesis. There is no
output-energy or output-entropy restriction. The pure refinement retains the
original d(rho,sigma)≤eps and substitutes only in the modulus. -/
theorem output_mutual_information_continuity {I J R : Type}
    [Countable I] [Nonempty I] [Countable J] [Nonempty J] [Countable R] [Nonempty R]
    (energy : I → ℝ≥0) (h22 : Condition22 energy)
    (Phi : QAlgorithms.Papers.Independent.Frontier18.P01.Channel I J)
    (E : ℝ) (hE : spectralGround energy ≤ E) :
    (∀ u : ℝ, spectralGround energy ≤ u → entropySupremum energy u < ⊤) ∧
    EnergyContinuity (fun X => coefficientEnergy energy (traceSecond X))
      (@outputMutualInformation I J R Phi) E (entropyModulus (entropySupremum energy) 2 2 E) ∧
    ∀ (rho sigma : PureState (I × R)) (eps : ℝ),
      coefficientEnergy energy (traceSecond rho.val.coefficients) ≤ ENNReal.ofReal E →
      coefficientEnergy energy (traceSecond sigma.val.coefficients) ≤ ENNReal.ofReal E →
      0 < eps → eps ≤ 1 / 2 → nuclearStateDistance rho.val sigma.val ≤ ENNReal.ofReal eps →
      |(outputMutualInformation Phi rho.val.coefficients).toReal -
        (outputMutualInformation Phi sigma.val.coefficients).toReal| ≤
        entropyModulus (entropySupremum energy) 2 2 E (eps ^ 2 / 2) := by sorry

end QAlgorithms.Papers.Independent.Support50.P18

end
