-- Prove2me | Theorems.Thm_TwoReLULayers_DepthCollapse_sign_region_congr
-- name    : TwoReLULayers.DepthCollapse.sign_region_congr
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T10:35:06.880081+00:00
-- url     : https://prove2.me/theorems/fb15a819-1acb-4631-8563-a8e486e303f6
-- title:
--   Corollary 18 — Both support-function congruence cases
-- statement:
--   For $n\ge2$ and every nonempty proper sign set $A\subset[n]$,
--   $$h_{P_A}\equiv0\quad(|A|\le n-2),\qquad h_{P_A}\equiv h_\Delta\quad(|A|=n-1).$$
--   Congruence means that the difference lies in the real span of support functions of nonempty polytopes of affine dimension at most $n-2$. Both cases are part of this statement. The second is congruence rather than pointwise equality: a translation contributes a linear function.
--
--   Differences from the source:
--   - encoding: finite Euclidean coordinates and finite index families → EuclideanSpace ℝ (Fin n), Fin k and pointwise function identities; reason: canonical coordinate identification and reindexing preserve every source instance
--   - encoding: support functions modulo lower affine dimension and almost everywhere on an affine space → the published supportFn, algebraic Submodule.span, integer dimension cutoffs and finite proper affine exceptional subspaces; reason: these express the source maximum, finite span and relative geometric convention exactly, including dimension zero
--   - encoding: vertex labels 1,...,n and marked positions 2,...,n-1 → zero-based Fin labels, bijective Order v and positive-valued marked positions; reason: subtracting one from labels and positions is a bijective reindexing; position one remains unconstrained
-- source:
--   Kilian Rueß, Florestan Brunck, Christoph Hertrich, Jack Stade, Amir Yehudayoff, Two ReLU layers is all you need, STOC 2027 submission #980 (October 2026), p. 22, Corollary 18

import Definitions.Def_TwoReLULayers_DepthCollapse_Construction

namespace TwoReLULayers.DepthCollapse

theorem sign_region_congr {n : ℕ} (hn : 2 ≤ n) (A : Finset (Fin n))
    (hA : A.Nonempty) (hproper : A ≠ Finset.univ) :
    (A.card ≤ n - 2 → Congr (support (signRegion A)) 0) ∧
    (A.card = n - 1 → Congr (support (signRegion A)) (support (simplex n))) := by sorry

end TwoReLULayers.DepthCollapse
