-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_SWS_entry_mem
-- name    : PositivityTheory.Rg.Cz.SWS.entry_mem
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:49:34.955457+00:00
-- url     : https://prove2.me/theorems/4769c3a9-4bc1-45fe-a7bb-efaa834a9453
-- title:
--   SWS: entry mem
-- statement:
--   The SWS construction uses the entry mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PSWStartA.lean#L86-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PSWStartA.lean#L86-L138

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PSWStartA
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
open PositivityTheory.Rg.Cz.SWS
variable {n : ℕ} {ι Γ : Type} [Fintype ι] [DecidableEq ι] [Group Γ] [TopologicalSpace Γ]
variable {bar : ι → ι} {κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ}

theorem PositivityTheory.Rg.Cz.SWS.entry_mem (hK : IsKD bar κ) {H : Set ι} (hH : ∀ τ, τ ∈ H ↔ bar τ ∉ H) (τ : ι) (i j : Fin n) :
    (fun k => κ τ k i j) ∈ Submodule.span ℂ (Mono κ H) := by sorry
