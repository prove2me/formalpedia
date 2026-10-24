-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P18_conditional_entropy_continuity_30
-- name    : QAlgorithms.Papers.Independent.Support50.P18.conditional_entropy_continuity_30
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T20:23:12.873269+00:00
-- url     : https://prove2.me/theorems/3e0b0bf1-1b9d-4242-8d17-118a76803674
-- title:
--   Section 5.1: extended conditional entropy continuity bound (30)
-- statement:
--   Under the Hamiltonian and energy assumptions of (29), define $I(A:B)_\rho=D(\rho_{AB}\|\rho_A\otimes\rho_B)$ and $H_e(A|B)_\rho=H(\rho_A)-I(A:B)_\rho$. The two terms in this last difference are finite on the energy ball, and $F_{H_A}(u)$ is finite for finite $u\ge E_0$. For $E\ge E_0$, both input $A$ energies at most $E$, and $0<\varepsilon=\frac12\|\rho-\sigma\|_1\le1/2$,
--
--   $$|H_e(A|B)_\rho-H_e(A|B)_\sigma|\le2\sqrt{2\varepsilon}\,F_{H_A}(E/\varepsilon)+g(\sqrt{2\varepsilon}).$$
--
--   The definition uses relative-entropy mutual information and allows infinite $B$ and joint entropies. Here $D$ is extended quantum relative entropy in nats and $g(x)=(1+x)h_2(x/(1+x))$.
-- source:
--   Adaptation of the Alicki-Fannes-Winter method for the set of states with bounded energy and its use, arXiv:1609.07044v5, PDF p. 11, Section 5.1

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

/-- Section 5.1, PDF p.11, (30): the relative-entropy definition (28) permits
infinite B and joint entropies. No such finiteness is required here. -/
theorem conditional_entropy_continuity_30 {I J : Type} [Countable I] [Nonempty I]
    [Countable J] [Nonempty J] (energy : I → ℝ≥0) (h22 : Condition22 energy)
    (E : ℝ) (hE : spectralGround energy ≤ E) :
    (∀ u : ℝ, spectralGround energy ≤ u → entropySupremum energy u < ⊤) ∧
    (∀ rho : State (I × J),
      coefficientEnergy energy (traceSecond rho.coefficients) ≤ ENNReal.ofReal E →
      extendedEntropyNats (traceSecond rho.coefficients) < ⊤ ∧
      marginalMutualInformation rho.coefficients < ⊤) ∧
    ∀ (rho sigma : State (I × J)) (eps : ℝ),
      coefficientEnergy energy (traceSecond rho.coefficients) ≤ ENNReal.ofReal E →
      coefficientEnergy energy (traceSecond sigma.coefficients) ≤ ENNReal.ofReal E →
      0 < eps → eps ≤ 1 / 2 → nuclearStateDistance rho sigma = ENNReal.ofReal eps →
      |extendedConditionalEntropy rho.coefficients - extendedConditionalEntropy sigma.coefficients| ≤
        entropyModulus (entropySupremum energy) 2 1 E eps := by sorry

end QAlgorithms.Papers.Independent.Support50.P18

end
