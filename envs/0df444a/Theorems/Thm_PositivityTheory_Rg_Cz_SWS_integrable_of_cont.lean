-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_SWS_integrable_of_cont
-- name    : PositivityTheory.Rg.Cz.SWS.integrable_of_cont
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:09:46.331556+00:00
-- url     : https://prove2.me/theorems/26ec0934-7548-4e0e-b4e2-f1cea7cca501
-- title:
--   SWS: integrable of cont
-- statement:
--   The SWS construction uses the integrable of cont property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PSWStartA.lean#L82-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PSWStartA.lean#L82-L84

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

theorem PositivityTheory.Rg.Cz.SWS.integrable_of_cont [MeasurableSpace Γ] [BorelSpace Γ] [CompactSpace Γ] (μ : MeasureTheory.Measure Γ)
    [MeasureTheory.IsFiniteMeasure μ] {f : Γ → ℂ} (hf : Continuous f) : MeasureTheory.Integrable f μ := by sorry
