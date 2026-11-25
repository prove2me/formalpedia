-- Prove2me | Theorems.Thm_PI_Dv_GLatHermW_isCM_cf
-- name    : PI.Dv.GLatHermW.isCM_cf
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:27:45.24549+00:00
-- url     : https://prove2.me/theorems/48432a1d-cac4-4e34-8bac-d73ea90bd4ea
-- title:
--   GLat Herm W: is CM cf
-- statement:
--   The GLat Herm W construction uses the is CM cf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianGroupLattices/IsCMFormEOf.lean#L18-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianGroupLattices/IsCMFormEOf.lean#L18-L20

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianGroupLattices_AsAlgebraHomEG
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianGroupLattices_IsCMFormEOf
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
open PI.Dv Formalism.BasicNotions
variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]

theorem PI.Dv.GLatHermW.isCM_cf (hS : StarIsConj K) (T : GoodSet K G) (g : G) : IsCM (cf T g) := by sorry
