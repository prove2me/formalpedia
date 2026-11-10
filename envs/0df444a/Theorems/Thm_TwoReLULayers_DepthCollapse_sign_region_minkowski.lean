-- Prove2me | Theorems.Thm_TwoReLULayers_DepthCollapse_sign_region_minkowski
-- name    : TwoReLULayers.DepthCollapse.sign_region_minkowski
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T10:35:14.513255+00:00
-- url     : https://prove2.me/theorems/f24fe6fc-2d1e-4de9-b9d7-097fee85a746
-- title:
--   Lemma 17 — Minkowski decomposition of sign regions
-- statement:
--   Let $n\ge2$ and $\varnothing\ne A\subsetneq[n]$. Write $\Delta_S=\operatorname{conv}\{e_i:i\in S\}$ and let $P_A$ be the closed sign region of $n\Delta-\mathbf1$. Then
--   $$P_A=\sum_{j\notin A}(\Delta_{A\cup\{j\}}-e_j).$$
--   The sum is a Minkowski sum of translated simplices, not a union. This identifies the sign regions geometrically before passing to support functions.
--
--   Differences from the source:
--   - encoding: finite Euclidean coordinates and finite index families → EuclideanSpace ℝ (Fin n), Fin k and pointwise function identities; reason: canonical coordinate identification and reindexing preserve every source instance
--   - encoding: vertex labels 1,...,n and marked positions 2,...,n-1 → zero-based Fin labels, bijective Order v and positive-valued marked positions; reason: subtracting one from labels and positions is a bijective reindexing; position one remains unconstrained
-- source:
--   Kilian Rueß, Florestan Brunck, Christoph Hertrich, Jack Stade, Amir Yehudayoff, Two ReLU layers is all you need, STOC 2027 submission #980 (October 2026), p. 21, Lemma 17

import Definitions.Def_TwoReLULayers_DepthCollapse_Construction

namespace TwoReLULayers.DepthCollapse

theorem sign_region_minkowski {n : ℕ} (hn : 2 ≤ n) (A : Finset (Fin n))
    (hA : A.Nonempty) (hproper : A ≠ Finset.univ) :
    signRegion A = minkowskiSum (Finset.univ \ A)
      (fun j => (fun x => x - basisVector j) '' simplexFace (insert j A)) := by sorry

end TwoReLULayers.DepthCollapse
