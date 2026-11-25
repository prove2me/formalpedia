-- Prove2me | Theorems.Thm_PositivityTheory_CW_FormEigenMonotone_norm_fib
-- name    : PositivityTheory.CW.FormEigenMonotone.norm_fib
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:50:25.284982+00:00
-- url     : https://prove2.me/theorems/35dd6c36-9c81-4e8b-9033-78eeb9da46c1
-- title:
--   Form Eigen Monotone: norm fib
-- statement:
--   The Form Eigen Monotone construction uses the norm fib property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/BasisSumOfOrthogonality.lean#L63-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/BasisSumOfOrthogonality.lean#L63-L67

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_BasisSumOfOrthogonality
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS
open PositivityTheory PositivityTheory.CW
open PositivityTheory.CW.FormEigenMonotone
variable {n : ℕ} {ε : Fin n → Bool} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {E : Fin n → Fin n → Module.End ℂ V} {ι : Type} {b : Module.Basis ι ℂ V} {μ : ι → ℝ}

theorem PositivityTheory.CW.FormEigenMonotone.norm_fib (hb : Orthonormal ℂ b) (f : V →ₗ[ℂ] ℂ) (F : Finset ι) :
    ‖∑ j ∈ F, starRingEnd ℂ (f (b j)) • b j‖ ^ 2 = ∑ j ∈ F, ‖f (b j)‖ ^ 2 := by sorry
