-- Prove2me | Theorems.Thm_PositivityTheory_KReal_filtX_succ_le
-- name    : PositivityTheory.KReal.filtX_succ_le
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:51:05.178023+00:00
-- url     : https://prove2.me/theorems/e07e46f6-bdef-57de-bb2d-1ff85b2e3833
-- title:
--   KReal: filt X succ le
-- statement:
--   The KReal construction uses the filt X succ le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreCasB.lean#L61-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreCasB.lean#L61-L76

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

theorem PositivityTheory.KReal.filtX_succ_le (X : I → Module.End ℂ M) (ι : V →ₗ[ℂ] M) (n : ℕ) :
    filtX X ι (n + 1) ≤ filtX X ι n ⊔
      Submodule.span ℂ {y | ∃ (w : Fin (n + 1) → I) (v : V), y = wordX X (List.ofFn w) (ι v)} := by sorry
