-- Prove2me | Theorems.Thm_PI_VolStabS_FFHS_mem_perp
-- name    : PI.VolStabS.FFHS.mem_perp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:07:50.876486+00:00
-- url     : https://prove2.me/theorems/b2d58024-b512-4d70-95f0-c63c82048b43
-- title:
--   FFHS: mem perp
-- statement:
--   The FFHS construction uses the mem perp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerVolume/LocDensFFHS.lean#L79-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerVolume/LocDensFFHS.lean#L79-L79

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensFF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensFFHS
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabS PI.VolStabS.FFHS
open Module
variable {K : Type} [Field K] {σ : K →+* K}
variable {V : Type} [AddCommGroup V] [Module K V] {h : V → V → K}

theorem PI.VolStabS.FFHS.mem_perp (hs : IsSq σ h) (e w : V) : w ∈ perp hs e ↔ h e w = 0 := by sorry
