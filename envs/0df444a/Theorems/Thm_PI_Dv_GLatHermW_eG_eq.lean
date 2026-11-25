-- Prove2me | Theorems.Thm_PI_Dv_GLatHermW_eG_eq
-- name    : PI.Dv.GLatHermW.eG_eq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:27:16.147362+00:00
-- url     : https://prove2.me/theorems/4395a142-d8a5-57d3-8f96-a1c297b4cb8b
-- title:
--   GLat Herm W: e G eq
-- statement:
--   The GLat Herm W construction uses the e G eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianGroupLattices/AsAlgebraHomEG.lean#L17-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianGroupLattices/AsAlgebraHomEG.lean#L17-L21

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianGroupLattices_StarMapTraceOfPowEqOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianGroupLattices_AsAlgebraHomEG
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.GLatHermW
open PI.Dv
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]

theorem PI.Dv.GLatHermW.eG_eq (T : GoodSet K G) : eG T = ∑ g : G, cf T g • MonoidAlgebra.of K G g := by sorry
