-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P18_channel_mutual_information_continuity
-- name    : QAlgorithms.Papers.Independent.Support50.P18.channel_mutual_information_continuity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T20:27:22.925836+00:00
-- url     : https://prove2.me/theorems/2e714091-3594-491c-a21b-5f0b05719cd2
-- title:
--   Corollary 6: channel mutual information as a function of the input state
-- statement:
--   Let $\Phi:A\to B$ be any CPTP channel, and define $I(\Phi,\rho)$ by applying $\Phi\otimes\mathrm{Id}$ to a purification of $\rho$ and taking output-reference mutual information. Suppose $H_A\ge0$ satisfies (22). For every finite $E\ge E_0$, this quantity is finite and uniformly continuous in trace distance on input states with mean energy at most $E$. The entropy capacity is finite at every finite budget above $E_0$, and for both input energies at most $E$ and $0<\varepsilon\le1/2$ bounding the half trace distance,
--
--   $$|I(\Phi,\rho)-I(\Phi,\sigma)|\le2\sqrt{2\varepsilon}\,F_{H_A}(E/\varepsilon)+2g(\sqrt{2\varepsilon}).$$
--
--   If $A$ is the $\ell$-mode oscillator, $F_{H_A}(u)$ may be replaced by $\ell\log((u+E_0)/(\ell E_*))+\ell$. A complete eigenbasis is available because (22) implies discrete spectrum. The oscillator realization in Lean is an equivalence of full eigenbasis indices preserving every energy level. No output-energy assumption is imposed.
-- source:
--   Adaptation of the Alicki-Fannes-Winter method for the set of states with bounded energy and its use, arXiv:1609.07044v5, PDF p. 18, Corollary 6

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

/-- Corollary 6, PDF pp.17--18, (50), including the oscillator replacement.
The accepted mutualInformation is the actual purification construction (49).
The eigenbasis is unrestricted because (22) implies discreteness; a realization
of the same spectrum as an oscillator transports the explicit bound (23).
No pure-state refinement is added to this corollary. -/
theorem channel_mutual_information_continuity {I J : Type}
    [Countable I] [Nonempty I] [Countable J] [Nonempty J]
    (energy : I → ℝ≥0) (h22 : Condition22 energy)
    (Phi : QAlgorithms.Papers.Independent.Frontier18.P01.Channel I J)
    (E : ℝ) (hE : spectralGround energy ≤ E) :
    (∀ u : ℝ, spectralGround energy ≤ u → entropySupremum energy u < ⊤) ∧
    EnergyContinuity (coefficientEnergy energy)
      (fun X => QAlgorithms.Papers.Independent.Frontier18.P01.mutualInformation X Phi.val)
      E (entropyModulus (entropySupremum energy) 2 2 E) ∧
    ∀ (ell : ℕ) (O : OscillatorParameters ell) (e : I ≃ (Fin ell → ℕ)),
      (∀ i, energy i = O.level (e i)) →
      EnergyContinuity (coefficientEnergy energy)
        (fun X => QAlgorithms.Papers.Independent.Frontier18.P01.mutualInformation X Phi.val)
        E (fun eps => 2 * Real.sqrt (2 * eps) * O.entropyUpper (E / eps) +
          2 * g (Real.sqrt (2 * eps))) := by sorry

end QAlgorithms.Papers.Independent.Support50.P18

end
