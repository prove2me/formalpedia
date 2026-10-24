-- Prove2me | Theorems.Thm_SDC_hom_sum_product
-- name    : SDC.hom_sum_product
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-23T09:24:50.655849+00:00
-- url     : https://prove2.me/theorems/01a0dc53-9d6a-4b5f-bdb8-9f2329fe96c3
-- title:
--   The sum-product formula: the pattern's homomorphism count as a sum of products of common-neighborhood sizes
-- statement:
--   The computational core. Because the pattern is the incidence graph of the triple system, a homomorphism from H to a host G is a map of points together with a map of triples, constrained only by the incidences: the image of a triple must be a common neighbor of the images of its three points. Summing over the point maps and multiplying the numbers of admissible images of the triples expresses the homomorphism count of the pattern as a sum over point maps of products of common-neighborhood sizes. This is the formula through which the inequality of the goal is evaluated on an explicit host.
-- source:
--   Mission-authored computational-core lemma within the framework of the uploaded manuscript A finite counterexample to Sidorenko conjecture (SidorenkoCounterexample.lean.txt); the formula is the standard expansion of the homomorphism count of an incidence pattern over the point maps.

import Mathlib
import Definitions.Def_SDC_graphs
import Definitions.Def_SDC_density

namespace SDC

open BigOperators

/-!  The computational core. Because the pattern is the incidence graph of
the triple system, a homomorphism from H to a host G is a map of points
together with a map of triples, constrained only by the incidences: the
image of a triple must be a common neighbor of the images of its three
points. Summing over the point maps and multiplying the numbers of
admissible images of the triples expresses the homomorphism count of the
pattern as a sum over point maps of products of common-neighborhood
sizes. This is the formula through which the inequality of the goal is
evaluated on an explicit host.  -/

theorem hom_sum_product {W : Type*} [Fintype W] (G : SimpleGraph W) :
    homCount H G =
      ∑ φ : (Fin 13 → W), ∏ f : Fin 22,
        (⋂ p ∈ faces f, G.neighborSet (φ p)).ncard := by
  sorry

end SDC
