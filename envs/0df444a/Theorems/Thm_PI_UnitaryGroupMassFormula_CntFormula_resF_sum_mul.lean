-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_CntFormula_resF_sum_mul
-- name    : PI.UnitaryGroupMassFormula.CntFormula.resF_sum_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:42:58.866244+00:00
-- url     : https://prove2.me/theorems/d310ae8a-e103-4cc6-aacf-76b531165740
-- title:
--   Cnt Formula: res F sum mul
-- statement:
--   The Cnt Formula construction uses the res F sum mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CountingFormula/DensGSDvr.lean#L35-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CountingFormula/DensGSDvr.lean#L35-L41

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CountingFormula_DensGSDvr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.CntFormula
open Classical ValuativeRel
variable (F : Type) [Field F] [ValuativeRel F]

theorem PI.UnitaryGroupMassFormula.CntFormula.resF_sum_mul {ι : Type} [Fintype ι] (c x : ι → F) (hc : ∀ i, c i ∈ 𝒪[F]) (hx : ∀ i, x i ∈ 𝒪[F]) :
    resF F (∑ i, c i * x i) = ∑ i, resF F (c i) * resF F (x i) := by sorry
