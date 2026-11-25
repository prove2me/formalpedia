-- Prove2me | Theorems.Thm_PIW_ClassFinD_idele_class_finite
-- name    : PIW.ClassFinD.idele_class_finite
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:49:46.736375+00:00
-- url     : https://prove2.me/theorems/566b3c9f-79b2-467c-a662-7efb0dafdfbd
-- title:
--   Class Fin D: idele class finite
-- statement:
--   The Class Fin D construction uses the idele class finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdeleClassFiniteness/LatticeIdealNonzero.lean#L43-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdeleClassFiniteness/LatticeIdealNonzero.lean#L43-L108

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdeleClassFiniteness_ExistsNeZeroMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdeleClassFiniteness_BorelGL
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdeleClassFiniteness_LatticeIdealNonzero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.ClassFinD
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Icf

theorem PIW.ClassFinD.idele_class_finite : IdeleClassFin := by sorry
