-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_exists_form_chart_1de3df5576aa
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_exists_form_chart_1de3df5576aa
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:00:09.724529+00:00
-- url     : https://prove2.me/theorems/5981e241-8895-4f5e-bb6a-47ea06a31e56
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman exists form chart 1de3df5576aa: P2 M Ground Theory Heights  Heights Kleiman exists form chart 1de3df5576aa
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman exists form chart 1de3df5576aa construction uses the P2 M Ground Theory Heights  Heights Kleiman exists form chart 1de3df5576aa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PStepDataJProper.lean#L65-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PStepDataJProper.lean#L65-L92

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepTwo
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PStepDataJProper
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_exists_form_chart_1de3df5576aa {I : Chart x} {P : Submodule (chartRing S x I) Ω} (hP : ChartInvertible P)
    {σ : Ω} (hσ : σ ∈ P) (hσ0 : σ ≠ 0) : ∃ (g : Poly S N) (e : ℕ), g.IsHomogeneous e ∧
      aeval x g ≠ 0 ∧ ∀ δ ∈ P, ∃ o ∈ twistMod S x (e : ℤ) I, aeval x g * δ = σ * o := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«exists_form_chart» := P2M_GroundTheory_Heights__Heights_Kleiman_exists_form_chart_1de3df5576aa
