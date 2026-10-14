-- Prove2me | Theorems.Thm_PigeonholeDesign_Upper_component_2
-- name    : PigeonholeDesign.Upper.component_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:13:06.870347+00:00
-- url     : https://prove2.me/theorems/16d6d17f-049e-4da4-9ca9-0d7bd9be297a
-- title:
--   Proof of Lemma 3, Component 2, pp. ec8–ec10 — the unmatched and the last T − τ subjects contribute O(T^{η/2}(log T)^{1/2})
-- statement:
--   Fix $\eta\in(0,1)$. There are a constant $C>0$ and a threshold $T_0$ such that for every even $T\ge T_0$ and every arrival sequence $x\in[0,1]^T$ the following holds. Run the pigeonhole design with the $\lceil T^{\eta}\rceil$ uniform pigeonholes of $[0,1]$, and let $\mathcal T_M$ be the set of matched subjects, so that its complement consists of the unmatched subjects $\mathcal T_U$ together with the last $T-\tau$ subjects. Then
--   $$\mathbb E\bigl[d_{A\setminus\mathcal T_M,\ B\setminus\mathcal T_M}\bigr]\ \le\ C\,T^{\frac\eta2}(\log T)^{\frac12}.$$
--
--   This is the second component of the proof of Lemma 3. Together with Component 1, and since a matching of the whole groups can be assembled from a matching inside $\mathcal T_M$ and one outside it, it yields Lemma 3.
--
--   **Formalization Note** Only the component's conclusion is stated. The paper's intermediate claim that, conditional on $H$, $H^0_\tau\sim\mathrm{Bin}(H,1/2)$ is not literally true because $H$ is read at the coin-dependent time $\tau$; it is not posed. The expectation is the average over all $2^T$ coin vectors; the complement of $\mathcal T_M$ is balanced on every run (both the whole run and $\mathcal T_M$ are balanced). $C$ and $T_0$ may depend on $\eta$ only. The logarithm is natural.
-- source:
--   Zhao and Zhou, Pigeonhole Design: Balancing Sequential Experiments from an Online Matching Perspective, arXiv:2201.12936v6, pp. ec8-ec10 (PDF pp. 46-48), proof of Lemma 3, Component 2 (conclusion)

import Mathlib
import Definitions.Def_PigeonholeDesign_Upper_Setting
import Definitions.Def_PigeonholeDesign_Upper_Stopping

namespace PigeonholeDesign.Upper

theorem component_2 (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℕ, ∀ T : ℕ, T₀ ≤ T → Even T →
      ∀ x : Fin T → ℝ, (∀ t, x t ∈ Set.Icc (0 : ℝ) 1) →
        (∑ coin : Fin T → Bool,
            discrepancyOn x (assign (uniformHole ⌈(T : ℝ) ^ η⌉₊) x coin)
              (matched (uniformHole ⌈(T : ℝ) ^ η⌉₊) x coin)ᶜ) / 2 ^ T
          ≤ C * ((T : ℝ) ^ (η / 2) * Real.sqrt (Real.log T)) := by sorry

end PigeonholeDesign.Upper
