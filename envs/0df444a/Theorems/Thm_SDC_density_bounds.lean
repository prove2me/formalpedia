-- Prove2me | Theorems.Thm_SDC_density_bounds
-- name    : SDC.density_bounds
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-23T09:23:08.168568+00:00
-- url     : https://prove2.me/theorems/63a6124a-9467-40e7-bb49-e1bc1fd99be9
-- title:
--   Host sanity: densities in the unit interval and monotonicity of the homomorphism count
-- statement:
--   Host sanity and monotonicity. For every finite nonempty host G: the homomorphism density of the pattern lies in the unit interval; the edge density of G lies in the unit interval; and whenever G is a subgraph of G' on the same vertex set, every homomorphism of the pattern into G is also one into G', so the homomorphism count is monotone in the host.
-- source:
--   Mission-authored sanity lemma within the framework of the uploaded manuscript A finite counterexample to Sidorenko conjecture (SidorenkoCounterexample.lean.txt).

import Mathlib
import Definitions.Def_SDC_graphs
import Definitions.Def_SDC_density

namespace SDC

/-!  Host sanity and monotonicity. For every finite nonempty host G: the
homomorphism density of the pattern lies in [0, 1], the edge density of
G lies in [0, 1], and whenever G is a subgraph of G' on the same vertex
set, every homomorphism of the pattern into G is also one into G', so
the homomorphism count is monotone in the host.  -/

theorem density_bounds {W : Type*} [Fintype W] [Nonempty W] (G : SimpleGraph W) :
    0 ≤ homDensity H G ∧
    homDensity H G ≤ 1 ∧
    0 ≤ edgeDensity G ∧
    edgeDensity G ≤ 1 ∧
    ∀ G' : SimpleGraph W, G ≤ G' → homCount H G ≤ homCount H G' := by
  sorry

end SDC
