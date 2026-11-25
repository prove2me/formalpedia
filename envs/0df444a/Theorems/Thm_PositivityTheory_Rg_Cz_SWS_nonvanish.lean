-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_SWS_nonvanish
-- name    : PositivityTheory.Rg.Cz.SWS.nonvanish
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:54:20.020818+00:00
-- url     : https://prove2.me/theorems/46836337-71e0-47f8-929b-405c12fcc978
-- title:
--   SWS: nonvanish
-- statement:
--   The SWS construction uses the nonvanish property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PSWStartB.lean#L53-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PSWStartB.lean#L53-L123

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

theorem PositivityTheory.Rg.Cz.SWS.nonvanish [MeasurableSpace Γ] [BorelSpace Γ] [CompactSpace Γ] [T2Space Γ] (μ : Measure Γ) [IsFiniteMeasure μ]
    [μ.IsOpenPosMeasure] (hK : IsKD bar κ) {H : Set ι} (hH : ∀ τ, τ ∈ H ↔ bar τ ∉ H)
    {f : Γ → ℂ} (hf : Continuous f) (x : Γ) (hx : f x ≠ 0) : ∃ g ∈ Mono κ H, ∫ k, g k * f k ∂μ ≠ 0 := by sorry
