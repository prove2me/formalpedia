-- Prove2me | Theorems.Thm_R03SP06_no_small_closed_separator
-- name    : R03SP06.no_small_closed_separator
-- status  : Proved
-- author  : @hao jia
-- created : 2026-09-17T10:45:14.97563+00:00
-- url     : https://prove2.me/theorems/90f733b8-28b5-4535-8183-481ad70cec5a
-- title:
--   R03 P3-factor structural result: no small closed separator
-- statement:
--   This is a source-faithful auxiliary theorem from the candidate formalization of the cubic P3-partition problem. It records the structural result `R03SP06.no_small_closed_separator` under exactly the explicit hypotheses in the Lean statement. It is a conditional reusable result and does not claim that the open root problem has been solved.
--
--   **Formalization Note** The Lean statement and direct proof were extracted from the cited candidate artifact; its source digest is ec5dc3a98178d2788a5e7cd85d25531d1d0a570718dd0b4ac584a97fa11d73ec.
-- source:
--   VibeMathing candidate artifact: research/artifacts/candidates/r03/parallel/sp06/separator_port_obstruction.lean; source SHA-256 ec5dc3a98178d2788a5e7cd85d25531d1d0a570718dd0b4ac584a97fa11d73ec; ProblemContract problem:opg-46613-p3-partition; candidate-only formalization.

import Mathlib
import Definitions.Def_cubic_p3_partition_models

namespace R03SP06

open R03SP06
open CubicP3Partition
variable {V : Type} [Fintype V] [DecidableEq V]
theorem no_small_closed_separator
    {G : SimpleGraph V} (h3 : ThreeVertexConnected G)
    {A B T : Finset V}
    (hA : A.Nonempty) (hB : B.Nonempty)
    (hAB : Disjoint A B) (hAT : Disjoint A T) (hBT : Disjoint B T)
    (hclosed : ∀ ⦃u v : V⦄, u ∈ A → G.Adj u v → v ∈ A ∪ T)
    (hT : T.card ≤ 2) : False := by sorry

end R03SP06
