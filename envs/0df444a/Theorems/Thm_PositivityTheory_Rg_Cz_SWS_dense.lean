-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_SWS_dense
-- name    : PositivityTheory.Rg.Cz.SWS.dense
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:49:16.233422+00:00
-- url     : https://prove2.me/theorems/2de9089a-92f4-4dd8-b7f5-47a092f3d29a
-- title:
--   SWS: dense
-- statement:
--   The SWS construction uses the dense property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PSWStartB.lean#L14-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PSWStartB.lean#L14-L51

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PSWStartA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PSWStartB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.REAL Matrix MeasureTheory
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open PositivityTheory.Rg.Cz.SWS
variable {n : ℕ} {ι Γ : Type} [Fintype ι] [DecidableEq ι] [Group Γ] [TopologicalSpace Γ]
  {bar : ι → ι} {κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ}

theorem PositivityTheory.Rg.Cz.SWS.dense [CompactSpace Γ] [T2Space Γ] (hK : IsKD bar κ) {H : Set ι} (hH : ∀ τ, τ ∈ H ↔ bar τ ∉ H)
    (g : C(Γ, ℂ)) : g ∈ closure {h : C(Γ, ℂ) | ⇑h ∈ Submodule.span ℂ (Mono κ H)} := by sorry
