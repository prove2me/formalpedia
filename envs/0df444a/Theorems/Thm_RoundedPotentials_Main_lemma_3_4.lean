-- Prove2me | Theorems.Thm_RoundedPotentials_Main_lemma_3_4
-- name    : RoundedPotentials.Main.lemma_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T08:34:54.0945+00:00
-- url     : https://prove2.me/theorems/54a18694-57a5-4a8f-b70e-d4f2db63e25f
-- title:
--   Lemma 3.4 — clipped-potential representation from root distances
-- statement:
--   For every feasible prescribed excess $b$ and every minimum-energy assignment $f^\star$ realizing it, let $d(v)$ be the infimum of lengths of all residual walks from the new root to $v$, and set $y_v=-d(v)$. Then each distance is finite, and
--   $$0\le y_v\le n-1,\qquad f^\star_{uv}=c_{uv}\operatorname{clip}(y_u-y_v)\quad(u,v\in V).$$
--   The identity includes all zero-capacity and absent pairs. The potentials are the specified shortest-distance potentials, not an arbitrary existential representation. This connects energy minimization to the potentials used for rounding.
--
--   Differences from the source:
--   - encoding: a finite vertex set V of size n → vertices Fin n and an edge list with distinct loopless ordered pairs; reason: relabeling preserves every flow and cut; m is the actual list length; zero capacities are explicitly allowed in §3
--   - encoding: shortest-path distance from a zero-edge root → EReal infimum over all finite residual walks from any start vertex; reason: the omitted initial root edge has length zero; finiteness and the real conversion equation are explicit conclusions, so no default is used
--   - generalization: §3 fixes W ≥ 1 and distinct terminals → W=0 and empty or singleton vertex sets are also allowed; reason: a zero-capacity or singleton loopless network has only the zero feasible assignment and all root distances zero; the empty case has no vertex or pair conclusions; all original instances remain included
-- source:
--   Ohad Trabelsi, STOC 2027 submission #1650 (October 2026), pp. 14–15, Lemma 3.4 and eq. (9)

import Mathlib
import Definitions.Def_RoundedPotentials_Main_EnergyResidual

namespace RoundedPotentials.Main
open scoped BigOperators

theorem lemma_3_4 {n W : ℕ} (I : Instance n W) (b : Fin n → ℝ)
    (f : Assignment n) (hf : MinimumEnergy I b f) :
    (∀ v, ∃ d : ℝ, rootDistance I f v = (d : EReal) ∧
      shortestPotential I f v = -d ∧ 0 ≤ -d ∧ -d ≤ (n : ℝ) - 1) ∧
    (∀ u v, f u v = induced I (shortestPotential I f) u v) := by sorry

end RoundedPotentials.Main
