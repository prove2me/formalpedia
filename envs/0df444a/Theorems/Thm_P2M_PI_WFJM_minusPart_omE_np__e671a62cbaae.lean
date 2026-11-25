-- Prove2me | Theorems.Thm_P2M_PI_WFJM_minusPart_omE_np__e671a62cbaae
-- name    : P2M_PI_WFJM_minusPart_omE_np__e671a62cbaae
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:41.795508+00:00
-- url     : https://prove2.me/theorems/da25eead-eeb4-47e5-b711-4874c31f589d
-- title:
--   P2 M PI WFJM minus Part om E np  e671a62cbaae: P2 M PI WFJM minus Part om E np  e671a62cbaae
-- statement:
--   The P2 M PI WFJM minus Part om E np  e671a62cbaae construction uses the P2 M PI WFJM minus Part om E np  e671a62cbaae property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/LoweringPartRightActionInlInr.lean#L464-L466
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/LoweringPartRightActionInlInr.lean#L464-L466

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_JointMultOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LoweringPartRightActionInlInr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action
open PI PI.WFJM
open MvPolynomial
open PI.FJM

theorem P2M_PI_WFJM_minusPart_omE_np__e671a62cbaae {p q r s : ℕ} (l l' : Ln p q r s) (h : linePos l = false) (h' : linePos l' = true)
    (P : Pol p q r s) : minusPart (omE l l') P = -(dd l' l P) := by sorry

alias «PI».«WFJM».«minusPart_omE_np'» := P2M_PI_WFJM_minusPart_omE_np__e671a62cbaae
