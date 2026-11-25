-- Prove2me | Theorems.Thm_PI_NUnimodLoc_UnitaryGroupMassFormula_TR_continuous_rmulQ
-- name    : PI.NUnimodLoc.UnitaryGroupMassFormula.TR.continuous_rmulQ
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:35:07.037576+00:00
-- url     : https://prove2.me/theorems/0d011991-085b-5f20-8e0f-2574aa19a888
-- title:
--   TR: continuous rmul Q
-- statement:
--   The TR construction uses the continuous rmul Q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalUnimodularLattice/Transf.lean#L39-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalUnimodularLattice/Transf.lean#L39-L41

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalUnimodularLattice_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalUnimodularLattice_Transf
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_ModW_continuous_rmulQ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Topology
noncomputable section
open PI PI.NUnimodLoc PI.NUnimodLoc.UnitaryGroupMassFormula PI.NUnimodLoc.UnitaryGroupMassFormula.TR
open PI Formalism.REAL
variable {m : ℕ}

theorem PI.NUnimodLoc.UnitaryGroupMassFormula.TR.continuous_rmulQ (a : Matrix (Fin m) (Fin m) ℂ) : Continuous (rmulQ (m := m) a) := by sorry
