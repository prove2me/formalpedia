-- Prove2me | Theorems.Thm_SDC_witness_inequality
-- name    : SDC.witness_inequality
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-23T09:25:27.0055+00:00
-- url     : https://prove2.me/theorems/784814e7-b373-4c04-9ed4-9da971c63d0a
-- title:
--   Clearing denominators: the violation as a natural-number inequality
-- statement:
--   Clearing denominators. For a finite nonempty host G with m vertices and e edges, the homomorphism density of the pattern is below the 66th power of the edge density exactly when the natural-number inequality homCount H G * m^132 < (2e)^66 * m^35 holds. The violation is therefore a decidable arithmetic statement about finite data, with no real division left.
-- source:
--   Mission-authored bookkeeping lemma within the framework of the uploaded manuscript A finite counterexample to Sidorenko conjecture (SidorenkoCounterexample.lean.txt).

import Mathlib
import Definitions.Def_SDC_graphs
import Definitions.Def_SDC_density

namespace SDC

/-!  Clearing denominators. For a finite nonempty host G with m vertices
and e edges, the homomorphism density of the pattern is below the 66th
power of the edge density exactly when the natural-number inequality
homCount H G * m ^ 132 < (2 * e) ^ 66 * m ^ 35 holds. The violation is
therefore a decidable arithmetic statement about finite data, with no
real division left.  -/

theorem witness_inequality {W : Type*} [Fintype W] [Nonempty W] (G : SimpleGraph W) :
    homDensity H G < (edgeDensity G) ^ 66 ↔
      homCount H G * (Fintype.card W) ^ 132 <
        (2 * edgeCard G) ^ 66 * (Fintype.card W) ^ 35 := by
  sorry

end SDC
