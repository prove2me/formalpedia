-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_SemiInvariantDeterminant_det_bar
-- name    : PositivityTheory.Rg.Cz.SemiInvariantDeterminant.det_bar
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:53:29.021522+00:00
-- url     : https://prove2.me/theorems/9bfe7abe-c6fe-4d6b-bb78-3f9d331cc0f1
-- title:
--   Semi Invariant Determinant: det bar
-- statement:
--   The Semi Invariant Determinant construction uses the det bar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PSemiZero.lean#L11-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PSemiZero.lean#L11-L17

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PSemiZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.REAL Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open PositivityTheory.Rg.Cz.SemiInvariantDeterminant

theorem PositivityTheory.Rg.Cz.SemiInvariantDeterminant.det_bar {ι Γ : Type} [Group Γ] [TopologicalSpace Γ] {n : ℕ} {bar : ι → ι}
    {κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ} (hK : IsKD bar κ) (τ : ι) (γ : Γ) :
    (κ (bar τ) γ).det = star (κ τ γ).det := by sorry
