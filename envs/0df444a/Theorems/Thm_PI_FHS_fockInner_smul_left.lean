-- Prove2me | Theorems.Thm_PI_FHS_fockInner_smul_left
-- name    : PI.FHS.fockInner_smul_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:20:22.68516+00:00
-- url     : https://prove2.me/theorems/5b322e70-35e2-433d-b466-99dc4ac4297e
-- title:
--   FHS: fock Inner smul left
-- statement:
--   The FHS construction uses the fock Inner smul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockHarmonicSplitting/FockInnerSelfReNonneg.lean#L85-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockHarmonicSplitting/FockInnerSelfReNonneg.lean#L85-L91

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

theorem PI.FHS.fockInner_smul_left (c : ℂ) (P Q : MvPolynomial σ ℂ) :
    FockH1Action.fockInner (c • P) Q = (starRingEnd ℂ) c * FockH1Action.fockInner P Q := by sorry
