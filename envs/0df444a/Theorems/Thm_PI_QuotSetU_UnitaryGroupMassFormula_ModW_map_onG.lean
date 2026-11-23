-- Prove2me | Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_ModW_map_onG
-- name    : PI.QuotSetU.UnitaryGroupMassFormula.ModW.map_onG
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T00:29:10.653183+00:00
-- url     : https://prove2.me/theorems/e17cae5c-2b0d-4946-b115-cd89446431ba
-- title:
--   Mod W: map on G
-- statement:
--   The Mod W construction uses the map on G property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryQuotientCompactness/ModBase.lean#L133-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryQuotientCompactness/ModBase.lean#L133-L139

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_SsetGroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_ModBase
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Topology
open scoped ENNReal NNReal
noncomputable section
open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula PI.QuotSetU.UnitaryGroupMassFormula.ModW
open PI
variable {m : ℕ}
variable {G : Set (Matrix (Fin m) (Fin m) ℂ)} {hG : IsMatGroup G}
open MG

theorem PI.QuotSetU.UnitaryGroupMassFormula.ModW.map_onG (μ : Measure (MtM m)) (hμ : IsHaarOnM G μ) : (onG hG μ).map val = μ := by sorry
