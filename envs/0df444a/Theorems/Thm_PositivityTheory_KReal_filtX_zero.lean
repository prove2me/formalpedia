-- Prove2me | Theorems.Thm_PositivityTheory_KReal_filtX_zero
-- name    : PositivityTheory.KReal.filtX_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:59:09.776836+00:00
-- url     : https://prove2.me/theorems/4efb18b6-b50b-4577-b5cb-eebfe6c855a5
-- title:
--   KReal: filt X zero
-- statement:
--   The KReal construction uses the filt X zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreCasB.lean#L21-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreCasB.lean#L21-L29

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCasB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped InnerProductSpace
open PositivityTheory PositivityTheory.KReal
variable {K I : Type} {M : Type} [AddCommGroup M] [Module ℂ M] {V : Type} [AddCommGroup V] [Module ℂ V]

theorem PositivityTheory.KReal.filtX_zero (X : I → Module.End ℂ M) (ι : V →ₗ[ℂ] M) : filtX X ι 0 = LinearMap.range ι := by sorry
