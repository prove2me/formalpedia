-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_CntFormula_dvr_prim_iff
-- name    : PI.UnitaryGroupMassFormula.CntFormula.dvr_prim_iff
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:38:09.462204+00:00
-- url     : https://prove2.me/theorems/980b5dfb-b1ce-4679-be8a-5ac6011fa5f2
-- title:
--   Cnt Formula: dvr prim iff
-- statement:
--   The Cnt Formula construction uses the dvr prim iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CountingFormula/DensGSDvr.lean#L173-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CountingFormula/DensGSDvr.lean#L173-L176

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
variable {F}

theorem PI.UnitaryGroupMassFormula.CntFormula.dvr_prim_iff [IsDiscreteValuationRing 𝒪[F]] {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ)
    {ι : Type} [Fintype ι] {n : ℕ} (X : ι → Fin n → F) (hX : ∀ i k, X i k ∈ 𝒪[F]) :
    (LinearIndependent F X ∧ SatF F X) ↔ LinearIndependent 𝓀[F] (redM F X) := by sorry
