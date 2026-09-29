-- Prove2me | Theorems.Thm_R03SP06_triangle_port_block_card_le_one
-- name    : R03SP06.triangle_port_block_card_le_one
-- status  : Proved
-- author  : @hao jia
-- created : 2026-09-17T10:46:06.752669+00:00
-- url     : https://prove2.me/theorems/2e94b718-675b-4533-b04a-5a4a7e0febbf
-- title:
--   R03 P3-factor structural result: triangle port block card le one
-- statement:
--   This is a source-faithful auxiliary theorem from the candidate formalization of the cubic P3-partition problem. It records the structural result `R03SP06.triangle_port_block_card_le_one` under exactly the explicit hypotheses in the Lean statement. It is a conditional reusable result and does not claim that the open root problem has been solved.
--
--   **Formalization Note** The Lean statement and direct proof were extracted from the cited candidate artifact; its source digest is d5c1f42c41c331b51f26cb63fa826906489e2c17631fbeebcc0c3c289460f718.
-- source:
--   VibeMathing candidate artifact: research/artifacts/candidates/r03/parallel/sp06/q3_triangle_external_port_card.lean; source SHA-256 d5c1f42c41c331b51f26cb63fa826906489e2c17631fbeebcc0c3c289460f718; ProblemContract problem:opg-46613-p3-partition; candidate-only formalization.

import Mathlib
import Definitions.Def_cubic_p3_partition_models

namespace R03SP06

open R03SP06
open CubicP3Partition
variable {V : Type} [Fintype V] [DecidableEq V]
theorem triangle_port_block_card_le_one
    {G : SimpleGraph V} [DecidableRel G.Adj] {T : Finset V} {t : V}
    (ht : t ∈ T)
    (hport : ∀ ⦃t u v : V⦄, t ∈ T → u ∉ T → v ∉ T →
      G.Adj t u → G.Adj t v → u = v) :
    (Finset.univ.filter (fun v : V => v ∉ T ∧ G.Adj t v)).card ≤ 1 := by sorry

end R03SP06
