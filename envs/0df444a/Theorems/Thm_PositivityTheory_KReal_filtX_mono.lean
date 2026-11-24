-- Prove2me | Theorems.Thm_PositivityTheory_KReal_filtX_mono
-- name    : PositivityTheory.KReal.filtX_mono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:59:01.049391+00:00
-- url     : https://prove2.me/theorems/2ee5fa78-cbb5-4859-be67-e244ede249ab
-- title:
--   KReal: filt X mono
-- statement:
--   The KReal construction uses the filt X mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreCasB.lean#L31-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreCasB.lean#L31-L35

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

theorem PositivityTheory.KReal.filtX_mono (X : I → Module.End ℂ M) (ι : V →ₗ[ℂ] M) {m n : ℕ} (h : m ≤ n) :
    filtX X ι m ≤ filtX X ι n := by sorry
