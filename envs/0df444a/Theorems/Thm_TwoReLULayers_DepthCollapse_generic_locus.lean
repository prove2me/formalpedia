-- Prove2me | Theorems.Thm_TwoReLULayers_DepthCollapse_generic_locus
-- name    : TwoReLULayers.DepthCollapse.generic_locus
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T10:35:12.861592+00:00
-- url     : https://prove2.me/theorems/6a47402f-7e52-48b4-93d8-b5f2268e2e73
-- title:
--   Thermostat genericity — the boundary exceptions are proper
-- statement:
--   For $n\ge2$ and any fixed $v\in[n]$, the locus where coordinates are nonzero and pairwise distinct, $y_v\ne-1$, and every allowed partial sum is different from $0$ and $-y_v$, is geometrically generic in $H_0$:
--   $$\text{these conditions hold outside finitely many proper affine subspaces of }H_0.$$
--   On this locus, if $y_v=\min_i y_i>-1$, the positive-coordinate count satisfies $1\le s\le n-1$. This includes $n=2$, when no partial-sum exceptions occur, and ensures the factorial formula is used on its intended domain.
--
--   Differences from the source:
--   - encoding: finite Euclidean coordinates and finite index families → EuclideanSpace ℝ (Fin n), Fin k and pointwise function identities; reason: canonical coordinate identification and reindexing preserve every source instance
--   - encoding: support functions modulo lower affine dimension and almost everywhere on an affine space → the published supportFn, algebraic Submodule.span, integer dimension cutoffs and finite proper affine exceptional subspaces; reason: these express the source maximum, finite span and relative geometric convention exactly, including dimension zero
--   - encoding: vertex labels 1,...,n and marked positions 2,...,n-1 → zero-based Fin labels, bijective Order v and positive-valued marked positions; reason: subtracting one from labels and positions is a bijective reindexing; position one remains unconstrained
-- source:
--   Kilian Rueß, Florestan Brunck, Christoph Hertrich, Jack Stade, Amir Yehudayoff, Two ReLU layers is all you need, STOC 2027 submission #980 (October 2026), p. 23, Proof of Lemma 20, genericity exclusions (unnumbered supporting bridge)

import Definitions.Def_TwoReLULayers_DepthCollapse_Construction

namespace TwoReLULayers.DepthCollapse

theorem generic_locus {n : ℕ} (hn : 2 ≤ n) (v : Fin n) :
    GeomAE (zeroHyperplane n) (Generic v) ∧
    ∀ y ∈ zeroHyperplane n, Generic v y →
      (-1 < y v ∧ ∀ i, y v ≤ y i) →
        1 ≤ positiveCount y ∧ positiveCount y ≤ n - 1 := by sorry

end TwoReLULayers.DepthCollapse
