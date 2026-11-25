-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_smulHom_inj
-- name    : PI.UnitaryGroupMassFormula.UnimodLocStd.smulHom_inj
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T06:01:45.323225+00:00
-- url     : https://prove2.me/theorems/e09f1866-3c06-5a32-b861-49790c3fc376
-- title:
--   Unimod Loc Std: smul Hom inj
-- statement:
--   The Unimod Loc Std construction uses the smul Hom inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularLocalStandard/RelIdxNeZeroOfLeLeft.lean#L16-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularLocalStandard/RelIdxNeZeroOfLeLeft.lean#L16-L20

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RelIdxNeZeroOfLeLeft
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem PI.UnitaryGroupMassFormula.UnimodLocStd.smulHom_inj {w : ℂ} (hw : w ≠ 0) : Function.Injective (smulHom (V := V) w) := by sorry
