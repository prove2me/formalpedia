-- Prove2me | Theorems.Thm_TwoReLULayers_DepthCollapse_simplex_decomposition
-- name    : TwoReLULayers.DepthCollapse.simplex_decomposition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T10:35:25.977453+00:00
-- url     : https://prove2.me/theorems/f9dda8cc-247f-457f-a76a-fd9de96be210
-- title:
--   Theorem 22 — Simplex decomposition with exact coefficient
-- statement:
--   For every $n\ge2$, the simplex $\Delta=\operatorname{conv}\{e_1,\ldots,e_n\}$ satisfies
--   $$h_\Delta\equiv\frac{(-1)^n}{n!}\sum_{v=1}^n\sum_\pi\sum_{M\subseteq\{2,\ldots,n-1\}}(-1)^{|M|}h_{K_{v,\pi,M}}.$$
--   The coefficient is exactly $(-1)^n/n!$. Congruence means that the generally nonzero remainder is a finite real linear combination of support functions of polytopes of affine dimension at most $n-2$.
--
--   Differences from the source:
--   - encoding: finite Euclidean coordinates and finite index families → EuclideanSpace ℝ (Fin n), Fin k and pointwise function identities; reason: canonical coordinate identification and reindexing preserve every source instance
--   - encoding: support functions modulo lower affine dimension and almost everywhere on an affine space → the published supportFn, algebraic Submodule.span, integer dimension cutoffs and finite proper affine exceptional subspaces; reason: these express the source maximum, finite span and relative geometric convention exactly, including dimension zero
--   - encoding: vertex labels 1,...,n and marked positions 2,...,n-1 → zero-based Fin labels, bijective Order v and positive-valued marked positions; reason: subtracting one from labels and positions is a bijective reindexing; position one remains unconstrained
-- source:
--   Kilian Rueß, Florestan Brunck, Christoph Hertrich, Jack Stade, Amir Yehudayoff, Two ReLU layers is all you need, STOC 2027 submission #980 (October 2026), p. 24, Theorem 22

import Definitions.Def_TwoReLULayers_DepthCollapse_Construction

namespace TwoReLULayers.DepthCollapse

theorem simplex_decomposition {n : ℕ} (hn : 2 ≤ n) :
    Congr (support (simplex n))
      (fun x => ((-1 : ℝ) ^ n / (Nat.factorial n : ℝ)) * signedKSupports n x) := by sorry

end TwoReLULayers.DepthCollapse
