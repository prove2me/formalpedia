-- Prove2me | Theorems.Thm_TwoReLULayers_DepthCollapse_construction_rational
-- name    : TwoReLULayers.DepthCollapse.construction_rational
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T10:35:26.889398+00:00
-- url     : https://prove2.me/theorems/f61bd6d6-d55b-4492-a868-f0f40a45c11e
-- title:
--   Rationality and compactness of the constructed polytopes
-- statement:
--   For $n\ge2$, all nonempty polytopes used in the explicit construction have rational vertices:
--   $$\Delta,\quad P_A\ (\varnothing\ne A\subsetneq[n]),\quad K_{v,\pi,M}\quad\text{are convex hulls of nonempty finite subsets of }\mathbb Q^n.$$
--   In particular they are nonempty compact real polytopes, so their support-function suprema are genuine finite maxima. This makes the rationality assertion used at the end of Section 8 an explicit supporting obligation.
--
--   Differences from the source:
--   - encoding: finite Euclidean coordinates and finite index families → EuclideanSpace ℝ (Fin n), Fin k and pointwise function identities; reason: canonical coordinate identification and reindexing preserve every source instance
--   - encoding: vertex labels 1,...,n and marked positions 2,...,n-1 → zero-based Fin labels, bijective Order v and positive-valued marked positions; reason: subtracting one from labels and positions is a bijective reindexing; position one remains unconstrained
--   - encoding: rational vertices → IsPolytopeOver (⊥ : Subfield ℝ); reason: the prime subfield of ℝ is exactly ℚ; the predicate requires an actual nonempty finite rational convex-hull witness
-- source:
--   Kilian Rueß, Florestan Brunck, Christoph Hertrich, Jack Stade, Amir Yehudayoff, Two ReLU layers is all you need, STOC 2027 submission #980 (October 2026), p. 24, Section 8, final paragraph; constructions in Sections 6.1 and 7.1

import Definitions.Def_TwoReLULayers_DepthCollapse_Construction

namespace TwoReLULayers.DepthCollapse

theorem construction_rational {n : ℕ} (hn : 2 ≤ n) :
    IsPolytopeOver (⊥ : Subfield ℝ) (simplex n) ∧
    (∀ A ∈ properSigns n, IsPolytopeOver (⊥ : Subfield ℝ) (signRegion A)) ∧
    (∀ v : Fin n, ∀ π : Order v, ∀ M ∈ (markedPositions n).powerset,
      IsPolytopeOver (⊥ : Subfield ℝ) (paramidK v π M)) := by sorry

end TwoReLULayers.DepthCollapse
