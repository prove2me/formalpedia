-- Prove2me | Theorems.Thm_P2M_Eden_radius__le_norm_a59aead72dbe
-- name    : P2M_Eden_radius__le_norm_a59aead72dbe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:16:38.270971+00:00
-- url     : https://prove2.me/theorems/584f707e-1cdb-599f-b95c-9487ab1bbc43
-- title:
--   P2 M Eden radius  le norm a59aead72dbe: P2 M Eden radius  le norm a59aead72dbe
-- statement:
--   The P2 M Eden radius  le norm a59aead72dbe construction uses the P2 M Eden radius  le norm a59aead72dbe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/UniformAttraction.lean#L89-L92
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/UniformAttraction.lean#L89-L92

import Definitions.Def_Eden_PhysicalRadius
import Definitions.Def_Eden_AttractorDistance
import Definitions.Def_Eden_StrictInvariance
import Definitions.Def_Eden_UniformAttraction
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden

theorem P2M_Eden_radius__le_norm_a59aead72dbe (p : PhaseSpace) : Real.sqrt (radiusSq₂ p) ≤ ‖p‖ := by sorry

alias «Eden».«radius₂_le_norm» := P2M_Eden_radius__le_norm_a59aead72dbe
