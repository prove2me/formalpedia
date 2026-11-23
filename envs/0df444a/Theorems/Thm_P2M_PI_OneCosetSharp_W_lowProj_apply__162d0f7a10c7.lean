-- Prove2me | Theorems.Thm_P2M_PI_OneCosetSharp_W_lowProj_apply__162d0f7a10c7
-- name    : P2M_PI_OneCosetSharp_W_lowProj_apply__162d0f7a10c7
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:18:39.040823+00:00
-- url     : https://prove2.me/theorems/ece7d5d3-06a1-4764-a093-b9a1d1455b85
-- title:
--   P2 M PI One Coset Sharp W low Proj apply  162d0f7a10c7: P2 M PI One Coset Sharp W low Proj apply  162d0f7a10c7
-- statement:
--   The P2 M PI One Coset Sharp W low Proj apply  162d0f7a10c7 construction uses the P2 M PI One Coset Sharp W low Proj apply  162d0f7a10c7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/projection2/MemFlagUnipotent.lean#L53-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/projection2/MemFlagUnipotent.lean#L53-L54

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_projection2_Assemble
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_projection2_MemFlagUnipotent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.OneCosetSharp PI.OneCosetSharp.W
open Loc LocE
variable {k : Type} [Field k] {n c : ℕ}

theorem P2M_PI_OneCosetSharp_W_lowProj_apply__162d0f7a10c7 (v : Fin (n + c) → k) (l : Fin (n + c)) : (XP : (Fin (n + c) → k) →ₗ[k] _) v l = if l.1 < n then v l else 0 := by sorry

alias «PI».«OneCosetSharp».«W».«lowProj_apply₂» := P2M_PI_OneCosetSharp_W_lowProj_apply__162d0f7a10c7
