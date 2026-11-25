-- Prove2me | Theorems.Thm_PIW_ClassFinD_diag_eq_diagGL
-- name    : PIW.ClassFinD.diag_eq_diagGL
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:47:35.195+00:00
-- url     : https://prove2.me/theorems/dd0c2614-d71b-4b41-9d69-042521e92494
-- title:
--   Class Fin D: diag eq diag GL
-- statement:
--   The Class Fin D construction uses the diag eq diag GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdeleClassFiniteness/BorelGL.lean#L47-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdeleClassFiniteness/BorelGL.lean#L47-L63

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdeleClassFiniteness_OhatCompact
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdeleClassFiniteness_BorelGL
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
open NumberField IsDedekindDomain

theorem PIW.ClassFinD.diag_eq_diagGL {R : Type} [CommRing R] {n : ℕ} (t : GL (Fin n) R) (ht : IsDiagM t.val) :
    ∃ τ : Fin n → Rˣ, t = diagGL n τ := by sorry
