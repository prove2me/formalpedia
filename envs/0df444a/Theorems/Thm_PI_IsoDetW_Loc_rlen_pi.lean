-- Prove2me | Theorems.Thm_PI_IsoDetW_Loc_rlen_pi
-- name    : PI.IsoDetW.Loc.rlen_pi
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:31:14.215409+00:00
-- url     : https://prove2.me/theorems/864580ec-24ef-4ca7-8256-2bac6d20a5d7
-- title:
--   Loc: rlen pi
-- statement:
--   The Loc construction uses the rlen pi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDeterminant/LocalPi.lean#L26-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDeterminant/LocalPi.lean#L26-L47

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_LidxAntisymm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_LocalPi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.IsoDetW PI.IsoDetW.Loc
open PI.IsoDetDefs

theorem PI.IsoDetW.Loc.rlen_pi {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] {M : ι → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] (X Z : ∀ i, Submodule R (M i)) :
    relative₂ (Submodule.pi Set.univ X) (Submodule.pi Set.univ Z) = ∑ i, relative₂ (X i) (Z i) := by sorry
