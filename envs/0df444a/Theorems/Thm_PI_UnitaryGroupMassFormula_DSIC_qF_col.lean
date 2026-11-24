-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_DSIC_qF_col
-- name    : PI.UnitaryGroupMassFormula.DSIC.qF_col
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:33:13.470136+00:00
-- url     : https://prove2.me/theorems/7bcb4752-7ef7-4a12-8b74-f3093df0f311
-- title:
--   DSIC: q F col
-- statement:
--   The DSIC construction uses the q F col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CentralCharacters/QuasiDeterminantConjInv.lean#L79-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CentralCharacters/QuasiDeterminantConjInv.lean#L79-L119

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CentralCharacters_CentralScalar
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CentralCharacters_QuasiDeterminantConjInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.DSIC
open Finset
open scoped Matrix

theorem PI.UnitaryGroupMassFormula.DSIC.qF_col {R : Type} [Ring R] [Algebra ℂ R] {n : ℕ} (E : Fin n → Fin n → R) (hE : Formalism.REAL.GlRel E)
    (B : Matrix (Fin n) (Fin n) ℂ) (u : ℂ) :
    qF (fun x a b => ∑ d, B d b • Formalism.REAL.Tm E x a d) u = B.det • Formalism.REAL.qdet E u := by sorry
