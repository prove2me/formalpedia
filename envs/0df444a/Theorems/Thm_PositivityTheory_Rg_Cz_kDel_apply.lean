-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_kDel_apply
-- name    : PositivityTheory.Rg.Cz.kDel_apply
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:10:51.618326+00:00
-- url     : https://prove2.me/theorems/c9527f81-5571-4548-97ce-068e891c87f7
-- title:
--   Cz: k Del apply
-- statement:
--   The Cz construction uses the k Del apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/KugaCoordinates/KugaAbsoluteValues/KSumApply.lean#L44-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/KugaCoordinates/KugaAbsoluteValues/KSumApply.lean#L44-L49

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

theorem PositivityTheory.Rg.Cz.kDel_apply (T : P →ₗ[ℝ] Module.End ℂ M) {β : Type} [Fintype β] (b : β → P) {n : ℕ}
    (θ : P [⋀^Fin (n + 1)]→ₗ[ℝ] M) (v : Fin n → P) :
    kDel T b θ v = ∑ i, T (b i) (θ (Matrix.vecCons (b i) v)) := by sorry
