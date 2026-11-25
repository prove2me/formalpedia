-- Prove2me | Theorems.Thm_PositivityTheory_KReal_filtX_fd
-- name    : PositivityTheory.KReal.filtX_fd
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:50:58.478588+00:00
-- url     : https://prove2.me/theorems/5916a42f-4794-583f-bb26-377fe0290623
-- title:
--   KReal: filt X fd
-- statement:
--   The KReal construction uses the filt X fd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreCasB.lean#L45-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreCasB.lean#L45-L59

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

theorem PositivityTheory.KReal.filtX_fd [Fintype I] [FiniteDimensional ℂ V] (X : I → Module.End ℂ M) (ι : V →ₗ[ℂ] M) (n : ℕ) :
    FiniteDimensional ℂ (filtX X ι n) := by sorry
