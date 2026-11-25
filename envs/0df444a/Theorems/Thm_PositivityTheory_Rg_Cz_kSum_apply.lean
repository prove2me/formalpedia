-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_kSum_apply
-- name    : PositivityTheory.Rg.Cz.kSum_apply
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:53:35.28536+00:00
-- url     : https://prove2.me/theorems/6fabad89-72af-4c40-954e-52f99ffdea9d
-- title:
--   Cz: k Sum apply
-- statement:
--   The Cz construction uses the k Sum apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/KugaCoordinates/KugaAbsoluteValues/KSumApply.lean#L33-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/KugaCoordinates/KugaAbsoluteValues/KSumApply.lean#L33-L38

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_KugaAbsoluteValues_KSumApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Fin Function
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
variable {P : Type} [AddCommGroup P] [Module ℝ P] {M : Type} [AddCommGroup M] [Module ℂ M]
  [Module ℝ M] [IsScalarTower ℝ ℂ M]

theorem PositivityTheory.Rg.Cz.kSum_apply {N : Type} [AddCommGroup N] [Module ℝ N] {ι β : Type} (s : Finset β)
    (F : β → P [⋀^ι]→ₗ[ℝ] N) (v : ι → P) : (∑ i ∈ s, F i) v = ∑ i ∈ s, F i v := by sorry
