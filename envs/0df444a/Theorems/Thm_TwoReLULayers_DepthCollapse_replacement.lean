-- Prove2me | Theorems.Thm_TwoReLULayers_DepthCollapse_replacement
-- name    : TwoReLULayers.DepthCollapse.replacement
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T10:35:12.59256+00:00
-- url     : https://prove2.me/theorems/9f7ad4bf-3ae7-4167-ac6d-c583f2858abe
-- title:
--   Lemma 21 — Replacement identity and its support consequence
-- statement:
--   For $n\ge2$, geometrically almost everywhere on $H_0$,
--   $$\sum_{v=1}^n\sum_\pi\sum_{M\subseteq\{2,\ldots,n-1\}}(-1)^{|M|}1_{K_{v,\pi,M}}=\sum_{\varnothing\ne A\subsetneq[n]}(-1)^{|A|-1}|A|!(n-|A|-1)!1_{P_A}.$$
--   Consequently, as functions on all $E_n$,
--   $$\sum_{v,\pi,M}(-1)^{|M|}h_{K_{v,\pi,M}}\equiv\sum_{\varnothing\ne A\subsetneq[n]}(-1)^{|A|-1}|A|!(n-|A|-1)!h_{P_A}.$$
--   Both the indicator identity and the support-function congruence belong to this item. The latter uses the real lower-dimensional span, not pointwise equality.
--
--   Differences from the source:
--   - encoding: finite Euclidean coordinates and finite index families → EuclideanSpace ℝ (Fin n), Fin k and pointwise function identities; reason: canonical coordinate identification and reindexing preserve every source instance
--   - encoding: support functions modulo lower affine dimension and almost everywhere on an affine space → the published supportFn, algebraic Submodule.span, integer dimension cutoffs and finite proper affine exceptional subspaces; reason: these express the source maximum, finite span and relative geometric convention exactly, including dimension zero
--   - encoding: vertex labels 1,...,n and marked positions 2,...,n-1 → zero-based Fin labels, bijective Order v and positive-valued marked positions; reason: subtracting one from labels and positions is a bijective reindexing; position one remains unconstrained
-- source:
--   Kilian Rueß, Florestan Brunck, Christoph Hertrich, Jack Stade, Amir Yehudayoff, Two ReLU layers is all you need, STOC 2027 submission #980 (October 2026), p. 24, Lemma 21

import Definitions.Def_TwoReLULayers_DepthCollapse_Construction

namespace TwoReLULayers.DepthCollapse

theorem replacement {n : ℕ} (hn : 2 ≤ n) :
    GeomAE (zeroHyperplane n)
      (fun y => (∑ v : Fin n, signedKIndicators v y) = signedRegionIndicators y) ∧
    Congr (signedKSupports n) (signedRegionSupports n) := by sorry

end TwoReLULayers.DepthCollapse
