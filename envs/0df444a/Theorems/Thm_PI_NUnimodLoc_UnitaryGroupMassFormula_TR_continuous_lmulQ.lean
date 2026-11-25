-- Prove2me | Theorems.Thm_PI_NUnimodLoc_UnitaryGroupMassFormula_TR_continuous_lmulQ
-- name    : PI.NUnimodLoc.UnitaryGroupMassFormula.TR.continuous_lmulQ
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:35:38.633782+00:00
-- url     : https://prove2.me/theorems/e715914b-7e58-46be-9492-6a42e3c4234c
-- title:
--   TR: continuous lmul Q
-- statement:
--   The TR construction uses the continuous lmul Q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalUnimodularLattice/Transf.lean#L35-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalUnimodularLattice/Transf.lean#L35-L37

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalUnimodularLattice_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalUnimodularLattice_Transf
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_ModW_continuous_lmulQ

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

theorem PI.NUnimodLoc.UnitaryGroupMassFormula.TR.continuous_lmulQ (a : Matrix (Fin m) (Fin m) ℂ) : Continuous (lmulQ (m := m) a) := by sorry
