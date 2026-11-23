-- Prove2me | Theorems.Thm_PI_IsoDetW_Loc_localization_pi
-- name    : PI.IsoDetW.Loc.localization_pi
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:29:51.205864+00:00
-- url     : https://prove2.me/theorems/9c1f213f-0ed1-4fa7-b757-fd90300f7879
-- title:
--   Loc: localization pi
-- statement:
--   The Loc construction uses the localization pi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDeterminant/LocalPi.lean#L10-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDeterminant/LocalPi.lean#L10-L24

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

theorem PI.IsoDetW.Loc.localization_pi {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] {M : ι → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] (p : Ideal R) [p.IsPrime]
    (X : ∀ i, Submodule R (M i)) :
    localization₂ p (Submodule.pi Set.univ X) = Submodule.pi Set.univ (fun i => localization₂ p (X i)) := by sorry
