-- Prove2me | Theorems.Thm_P2M_Eden_radius__le_norm_83bb5ee710e2
-- name    : P2M_Eden_radius__le_norm_83bb5ee710e2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:16:07.798186+00:00
-- url     : https://prove2.me/theorems/5d26f277-847c-4834-847c-f6f2a4f1e383
-- title:
--   P2 M Eden radius  le norm 83bb5ee710e2: P2 M Eden radius  le norm 83bb5ee710e2
-- statement:
--   The P2 M Eden radius  le norm 83bb5ee710e2 construction uses the P2 M Eden radius  le norm 83bb5ee710e2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/UniformAttraction.lean#L84-L87
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/UniformAttraction.lean#L84-L87

import Definitions.Def_Eden_PhysicalRadius
import Definitions.Def_Eden_AttractorDistance
import Definitions.Def_Eden_StrictInvariance
import Definitions.Def_Eden_UniformAttraction
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden

theorem P2M_Eden_radius__le_norm_83bb5ee710e2 (p : PhaseSpace) : Real.sqrt (radiusSq₁ p) ≤ ‖p‖ := by sorry

alias «Eden».«radius₁_le_norm» := P2M_Eden_radius__le_norm_83bb5ee710e2
