-- Prove2me | Theorems.Thm_PI_FockOneDegW_Core_key
-- name    : PI.FockOneDegW.Core.key
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:56:38.751289+00:00
-- url     : https://prove2.me/theorems/0d8d3958-5576-47ce-ac8e-3353197ab9be
-- title:
--   Core: key
-- statement:
--   The Core construction uses the key property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockDegreeOne/ExistsMonomialWeight.lean#L30-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockDegreeOne/ExistsMonomialWeight.lean#L30-L34

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OneDegOfHalves
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_EqZeroOfFockInnerSelfRe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OmEDiagMonomial
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_ExistsMonomialWeight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action MvPolynomial
open PI PI.FockOneDegW PI.FockOneDegW.Core
open PI.FockOneDegW PI.FockOneDegW.Inner PI.FockOneDegW.Diag

theorem PI.FockOneDegW.Core.key {σ : Type*} (v : MvPolynomial σ ℂ) (ac ad bc bd : σ) (hne : bc ≠ ad) :
    fockInner (pderiv ac (pderiv ad v)) (pderiv bc (pderiv bd v)) =
      fockInner (X bc * pderiv ac v) (X ad * pderiv bd v) := by sorry
