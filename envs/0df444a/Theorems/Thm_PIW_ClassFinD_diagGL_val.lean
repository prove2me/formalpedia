-- Prove2me | Theorems.Thm_PIW_ClassFinD_diagGL_val
-- name    : PIW.ClassFinD.diagGL_val
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:47:39.123296+00:00
-- url     : https://prove2.me/theorems/f01f446b-cbea-4dc7-bfd7-f8bd9ca1b8d9
-- title:
--   Class Fin D: diag GL val
-- statement:
--   The Class Fin D construction uses the diag GL val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdeleClassFiniteness/BorelGL.lean#L37-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdeleClassFiniteness/BorelGL.lean#L37-L38

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

theorem PIW.ClassFinD.diagGL_val {R : Type} [CommRing R] (n : ℕ) (τ : Fin n → Rˣ) :
    (diagGL n τ).val = Matrix.diagonal fun i => (τ i : R) := by sorry
