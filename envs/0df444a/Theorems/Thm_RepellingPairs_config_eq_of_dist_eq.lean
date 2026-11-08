-- Prove2me | Theorems.Thm_RepellingPairs_config_eq_of_dist_eq
-- name    : RepellingPairs.config_eq_of_dist_eq
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:02:01.870326+00:00
-- url     : https://prove2.me/theorems/8e5e45d4-f256-4598-be19-216d47f176a6
-- title:
--   §3.4, p.13 — a configuration is determined by its metric and degrees
-- statement:
--   Let $C,C'$ be configurations on $n$ points of a circle, loops allowed, with equal degree at every point. If $\mathrm{dist}_C(\bar i,\bar j)=\mathrm{dist}_{C'}(\bar i,\bar j)$ for all bars, then $C=C'$.
--
--   In the proof of Theorem 1 this separates the case $C=C'$ from the case $C\succ C'$.
--
--   Differences from the source:
--   - generalization: configurations with no mention of loops; same induced metric implies C = C′ → loops allowed, with equal degrees as a hypothesis; reason: equal degrees cannot be dropped with loops: {(1,1)} and ∅ induce the same metric. Without loops, the cuts around single points already force equal degrees, so this specializes to the printed statement
-- source:
--   Chen, Pylyavskyy, Tan, Paths and Intersections: Repelling Pairs, arXiv:2607.02883 (version of October 23, 2026), §3.4, p.13

import Mathlib
import Definitions.Def_RepellingPairs_Config

set_option autoImplicit false

namespace RepellingPairs

/-- **§3.4, uniqueness.** Configurations inducing the same metric on the bars, with equal degrees at every point, are
equal. Chen, Pylyavskyy, Tan, arXiv:2607.02883 (version of October 23, 2026), §3.4, p.13.

**Formalization Note.** Loops are allowed, which the page does not consider. Equal degrees cannot be dropped then:
`{(1,1)}` and `∅` induce the same metric. Without loops the cuts around single points force equal degrees, so this
covers the page's statement. -/
theorem config_eq_of_dist_eq {n : ℕ} (C C' : Config n)
    (hdeg : ∀ t, Config.deg C t = Config.deg C' t)
    (h : ∀ i j, Config.dist C i j = Config.dist C' i j) : C = C' := by sorry

end RepellingPairs
