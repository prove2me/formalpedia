-- Prove2me | Theorems.Thm_PI_FHS_fockInner_smul_right
-- name    : PI.FHS.fockInner_smul_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:20:17.675081+00:00
-- url     : https://prove2.me/theorems/85a2e5eb-a351-40f4-9dba-36b8f0908e61
-- title:
--   FHS: fock Inner smul right
-- statement:
--   The FHS construction uses the fock Inner smul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockHarmonicSplitting/FockInnerSelfReNonneg.lean#L93-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockHarmonicSplitting/FockInnerSelfReNonneg.lean#L93-L98

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

theorem PI.FHS.fockInner_smul_right (c : ℂ) (P Q : MvPolynomial σ ℂ) :
    FockH1Action.fockInner P (c • Q) = c * FockH1Action.fockInner P Q := by sorry
