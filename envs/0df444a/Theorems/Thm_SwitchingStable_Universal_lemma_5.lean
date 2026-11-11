-- Prove2me | Theorems.Thm_SwitchingStable_Universal_lemma_5
-- name    : SwitchingStable.Universal.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:57:31.192193+00:00
-- url     : https://prove2.me/theorems/6a83b72f-9b96-4722-bdce-50219d618f87
-- title:
--   Lemma 5 — Next-owner witnesses
-- statement:
--   Fix a stable matching $\mu$ and direction $\varepsilon\in\{-1,1\}$. Let $p_{u,j}^\varepsilon$ be the owner of the stable partner at directional distance $j$ and let $f$ be the next-owner map on active men. Every such owner is active; $f$ maps active men to active men without fixed points. If $h=f(p_{u,j}^\varepsilon)\ne u$, then
--   $$\nu(h)=\mu(h)\Longrightarrow\varepsilon(\operatorname{idx}_u(\nu)-q_u)<j\qquad(\nu\in\mathrm{Stab}(I)).$$
--   Thus the full next-owner implication supplies an unchanged-edge witness at every valid distance.
--
--   Differences from the source:
--   - encoding: The partial next-owner map on active men and signed index differences → An explicit two-valued direction; integer subtraction; next equals the coordinate off its active domain; reason: All assertions about next retain the active-domain guard; no negative motion is truncated.
-- source:
--   Hao Xu, Jinshan Zhang, Feng Wang, STOC 2027 submission #170 (October 2026), p. 4, PDF p. 5, Lemma 5

import Mathlib
import Definitions.Def_SwitchingStable_Universal_Transport

namespace SwitchingStable.Universal

open MeasureTheory

theorem lemma_5 {n : ℕ} (I : StableMatching.Instance n)
    (μ : StableMatching.Matching n) (hμ : I.IsStable μ) (ε : Direction) :
    (∀ (u : Fin n) (j : ℕ), 1 ≤ j → j ≤ distance I μ u ε →
      Active I μ ε (owner I μ ε u j)) ∧
    (∀ u : Fin n, Active I μ ε u → Active I μ ε (next I μ ε u) ∧ next I μ ε u ≠ u) ∧
    (∀ (u : Fin n) (j : ℕ), 1 ≤ j → j ≤ distance I μ u ε →
      next I μ ε (owner I μ ε u j) ≠ u →
      Witness I μ ε u (next I μ ε (owner I μ ε u j)) j) := by sorry

end SwitchingStable.Universal
