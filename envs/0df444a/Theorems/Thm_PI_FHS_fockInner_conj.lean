-- Prove2me | Theorems.Thm_PI_FHS_fockInner_conj
-- name    : PI.FHS.fockInner_conj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:20:41.447595+00:00
-- url     : https://prove2.me/theorems/086c206e-81a0-4f0a-969f-493902b58105
-- title:
--   FHS: fock Inner conj
-- statement:
--   The FHS construction uses the fock Inner conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockHarmonicSplitting/FockInnerSelfReNonneg.lean#L122-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockHarmonicSplitting/FockInnerSelfReNonneg.lean#L122-L128

import Definitions.Def_Formalism_PeriodIntegrals_JointBlockShapes_MinusPart
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockHarmonicSplitting_FockInnerSelfReNonneg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PI PI.FHS
variable {σ : Type*}

theorem PI.FHS.fockInner_conj (P Q : MvPolynomial σ ℂ) :
    (starRingEnd ℂ) (FockH1Action.fockInner Q P) = FockH1Action.fockInner P Q := by sorry
