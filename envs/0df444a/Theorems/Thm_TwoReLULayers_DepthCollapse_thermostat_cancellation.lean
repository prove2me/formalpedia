-- Prove2me | Theorems.Thm_TwoReLULayers_DepthCollapse_thermostat_cancellation
-- name    : TwoReLULayers.DepthCollapse.thermostat_cancellation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T10:35:05.049007+00:00
-- url     : https://prove2.me/theorems/46a8742c-c557-4c94-9f56-a76cf3d82e53
-- title:
--   Lemma 20 — Thermostat cancellation
-- statement:
--   Let $n\ge2$ and fix $v\in[n]$. For geometrically almost every $y\in H_0$, put $s=|\{i:y_i>0\}|$. Then
--   $$\sum_\pi\sum_{M\subseteq\{2,\ldots,n-1\}}(-1)^{|M|}1_{K_{v,\pi,M}}(y)=\begin{cases}(-1)^{s-1}s!(n-1-s)!,&y_v=\min_i y_i>-1,\\0,&\text{otherwise}.\end{cases}$$
--   The outer sum uses all bijective orderings of $[n]\setminus\{v\}$. The exceptional finite family may depend on $v$. The zero branch and the precise signed factorial count are retained.
--
--   Differences from the source:
--   - encoding: finite Euclidean coordinates and finite index families → EuclideanSpace ℝ (Fin n), Fin k and pointwise function identities; reason: canonical coordinate identification and reindexing preserve every source instance
--   - encoding: support functions modulo lower affine dimension and almost everywhere on an affine space → the published supportFn, algebraic Submodule.span, integer dimension cutoffs and finite proper affine exceptional subspaces; reason: these express the source maximum, finite span and relative geometric convention exactly, including dimension zero
--   - encoding: vertex labels 1,...,n and marked positions 2,...,n-1 → zero-based Fin labels, bijective Order v and positive-valued marked positions; reason: subtracting one from labels and positions is a bijective reindexing; position one remains unconstrained
-- source:
--   Kilian Rueß, Florestan Brunck, Christoph Hertrich, Jack Stade, Amir Yehudayoff, Two ReLU layers is all you need, STOC 2027 submission #980 (October 2026), p. 22, Lemma 20

import Definitions.Def_TwoReLULayers_DepthCollapse_Construction

namespace TwoReLULayers.DepthCollapse

theorem thermostat_cancellation {n : ℕ} (hn : 2 ≤ n) (v : Fin n) :
    GeomAE (zeroHyperplane n) (fun y => signedKIndicators v y = thermostatValue v y) := by sorry

end TwoReLULayers.DepthCollapse
