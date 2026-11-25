-- Prove2me | Theorems.Thm_PIW_AdelClassFin_svR_det
-- name    : PIW.AdelClassFin.svR_det
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:47:46.927698+00:00
-- url     : https://prove2.me/theorems/07cfca88-6703-4054-882d-2ca2139e6775
-- title:
--   Adel Class Fin: sv R det
-- statement:
--   The Adel Class Fin construction uses the sv R det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/SuccessiveVectorReal.lean#L20-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/SuccessiveVectorReal.lean#L20-L25

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_PartShortOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_SuccessiveVectorReal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.AdelClassFin
open Formalism.UG NumberField Matrix
open scoped ComplexOrder
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem PIW.AdelClassFin.svR_det (eq : κ ≃ ι) (X : Matrix ι κ ℂ) (B : Matrix ι ι ℂ) :
    (Xᴴ * B * X).det = star (X.submatrix eq id).det * B.det * (X.submatrix eq id).det := by sorry
