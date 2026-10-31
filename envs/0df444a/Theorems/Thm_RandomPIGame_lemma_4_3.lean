-- Prove2me | Theorems.Thm_RandomPIGame_lemma_4_3
-- name    : RandomPIGame.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:26:43.669989+00:00
-- url     : https://prove2.me/theorems/5beeeaed-54cc-4a36-92f0-f0180e8cbcb8
-- title:
--   Lemma 4.3: truncation is continuous, $v_{\omega_t}\downarrow v_\omega$, and $v$ is upper semicontinuous, hence measurable
-- statement:
--   1. For $t\in\mathbb N_+$, the map $\Omega\to\Omega$, $\omega\mapsto\omega_t$, is continuous.
--   2. For $t\in\mathbb N_+$, the map $v_t:\Omega\to\mathbb R$, $\omega\mapsto v_{\omega_t}$, is continuous.
--   3. For each $\omega\in\Omega$, $v_{\omega_0}\ge v_{\omega_1}\ge\cdots$ is a non-increasing sequence converging to $v_\omega$. Consequently the map $v:\Omega\to\mathbb R$, $\omega\mapsto v_\omega$, is upper semicontinuous, hence measurable.
--
--   Measurability of the value is not automatic: the paper recalls that the value of a Borel-parameterized infinite perfect information game need not be Borel measurable. This lemma is what makes $\mathbb P(v<k)$ meaningful and reduces it to finite horizons.
--
--   Differences from the source:
--   - encoding: a play is a finite or infinite sequence of nodes, and the payoff is the infimum of its capacities → a play is a sequence indexed by ℕ that stays at an end node once reached, and the payoff is the infimum over all stages; reason: stuttering does not change the set of capacities visited
--   - encoding: v_ω is the common value of sup inf and inf sup → value is defined as the sup inf; reason: the equality with inf sup is the milestone section2_value; the strategy types are nonempty and payoffs lie in [0, γ(⊘)], so both real extrema are genuine
--   - encoding: capacities and thresholds k in [0, ∞) → capacities and thresholds k in ℝ≥0; reason: Lean convention; the same numbers
-- source:
--   Flesch, Predtetchinski & Suomala, Random perfect information games, arXiv:2104.10528v1, Lemma 4.3, p.14

import Mathlib
import Definitions.Def_RandomPIGame_Primitive
import Definitions.Def_RandomPIGame_Game
import Definitions.Def_RandomPIGame_Value

open Filter Topology

namespace RandomPIGame

/-- Truncation and the value. arXiv:2104.10528v1, Lemma 4.3, p.14.

1. For `t ∈ ℕ₊`, the map `ω ↦ ω_t` is continuous.
2. For `t ∈ ℕ₊`, the map `v_t : ω ↦ v_{ω_t}` is continuous.
3. For each `ω`, `v_{ω_0} ≥ v_{ω_1} ≥ ⋯` is a non-increasing sequence converging to `v_ω`.
   Consequently `v : ω ↦ v_ω` is upper semicontinuous, hence measurable.

**Formalization Note.** Items 1 and 2 keep the printed `t ∈ ℕ₊`; item 3 runs from `t = 0`, as
printed. -/
theorem lemma_4_3 :
    (∀ t : ℕ, 1 ≤ t → Continuous fun ω : Game => ω.trunc t) ∧
      (∀ t : ℕ, 1 ≤ t → Continuous fun ω : Game => (ω.trunc t).value) ∧
      (∀ ω : Game, Antitone (fun t : ℕ => (ω.trunc t).value) ∧
        Tendsto (fun t : ℕ => (ω.trunc t).value) atTop (𝓝 ω.value)) ∧
      UpperSemicontinuous Game.value ∧
      Measurable Game.value := by sorry

end RandomPIGame
