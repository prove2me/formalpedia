-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P18_relative_entanglement_continuity
-- name    : QAlgorithms.Papers.Independent.Support50.P18.relative_entanglement_continuity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T20:24:45.312296+00:00
-- url     : https://prove2.me/theorems/7d9c84d8-83da-4943-ab36-1e0b374cbfb9
-- title:
--   Proposition 4: one-subsystem energy continuity of ER and regularized ER
-- statement:
--   Let $A,B$ be infinite-dimensional separable quantum systems. Define $E_R(\rho)=\inf_{\omega\in\mathrm{Sep}}D(\rho\|\omega)$, where $\mathrm{Sep}$ is the trace-norm closed convex hull of product states, and define $E_R^\infty(\rho)=\lim_{n\to\infty}E_R(\rho^{\otimes n})/n$, equivalently the extended infimum over positive $n$. Suppose $H_A\ge0$ satisfies condition (22), and let $E\ge E_0$. Both quantities are finite and uniformly continuous in trace distance on the joint states with $A$ energy at most $E$. For either quantity $\mathcal E$ and any two such states with $\frac12\|\rho-\sigma\|_1\le\varepsilon\le1/2$, $\varepsilon>0$,
--
--   $$|\mathcal E(\rho)-\mathcal E(\sigma)|\le\sqrt{2\varepsilon}\,F_{H_A}(E/\varepsilon)+g(\sqrt{2\varepsilon}).$$
--
--   The entropy supremum $F_{H_A}$ is finite at every finite budget above $E_0$. If $A$ is an oscillator, $F_{H_A}$ can be replaced by $\ell\log((u+E_0)/(\ell E_*))+\ell$ at $u=E/\varepsilon$. This requires no restriction on $B$ energy or entropy and includes no additional pure-state claim.
-- source:
--   Adaptation of the Alicki-Fannes-Winter method for the set of states with bounded energy and its use, arXiv:1609.07044v5, PDF p. 15, Proposition 4

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

/-- Proposition 4, PDF pp.14--16, (40), for ER and its actual regularization.
A and B are infinite dimensional. There is no restriction on B's entropy or
energy and no pure-state refinement is appended. The oscillator replacement
uses the full zero-point-energy majorant (23). -/
theorem relative_entanglement_continuity {I J : Type}
    [Countable I] [Infinite I] [Countable J] [Infinite J]
    (energy : I → ℝ≥0) (h22 : Condition22 energy)
    (E : ℝ) (hE : spectralGround energy ≤ E) :
    (∀ u : ℝ, spectralGround energy ≤ u → entropySupremum energy u < ⊤) ∧
    (∀ f ∈ ({countableRelativeEntanglementNats, regularizedCountableEntanglementNats} :
        Set (Matrix (I × J) (I × J) ℂ → ℝ≥0∞)),
      EnergyContinuity (fun X => coefficientEnergy energy (traceSecond X)) f E
        (entropyModulus (entropySupremum energy) 1 1 E)) ∧
    ∀ (ell : ℕ) (O : OscillatorParameters ell) (e : I ≃ (Fin ell → ℕ)),
      (∀ i, energy i = O.level (e i)) →
      ∀ f ∈ ({countableRelativeEntanglementNats, regularizedCountableEntanglementNats} :
        Set (Matrix (I × J) (I × J) ℂ → ℝ≥0∞)),
        EnergyContinuity (fun X => coefficientEnergy energy (traceSecond X)) f E
          (fun eps => Real.sqrt (2 * eps) * O.entropyUpper (E / eps) +
            g (Real.sqrt (2 * eps))) := by sorry

end QAlgorithms.Papers.Independent.Support50.P18

end
