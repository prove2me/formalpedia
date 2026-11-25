-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_Hypotheses__BlowupGlue_blowup_of_eq_on_open_2be0684b2feb
-- name    : P2M_GlobalTheory_CompanionTheory_Hypotheses__BlowupGlue_blowup_of_eq_on_open_2be0684b2feb
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T14:42:31.303058+00:00
-- url     : https://prove2.me/theorems/1ce3b2bf-83f6-46f1-959b-b1c175783da0
-- title:
--   P2 M Global Theory Companion Theory Hypotheses  Blowup Glue blowup of eq on open 2be0684b2feb: P2 M Global Theory Companion Theory Hypotheses  Blowup Glue blowup of eq on open 2be0684b2feb
-- statement:
--   The P2 M Global Theory Companion Theory Hypotheses  Blowup Glue blowup of eq on open 2be0684b2feb construction uses the P2 M Global Theory Companion Theory Hypotheses  Blowup Glue blowup of eq on open 2be0684b2feb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/BlowupOfAgreeingIdealCartier.lean#L88-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/BlowupOfAgreeingIdealCartier.lean#L88-L134

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WChartsB
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_BlowupOfAgreeingIdealCartier
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.BlowupGlue

theorem P2M_GlobalTheory_CompanionTheory_Hypotheses__BlowupGlue_blowup_of_eq_on_open_2be0684b2feb : ∀ {X₁ X₂ : Scheme.{0}} (π : X₂ ⟶ X₁) (Z Z' : X₁.IdealSheafData) (O₁ O₂ : X₁.Opens),
    FinalTheorems.Blowup π Z → O₁ ⊔ O₂ = ⊤ → Z'.comap O₁.ι = Z.comap O₁.ι → (∀ x ∈ O₂, x ∉ Z'.support) →
    FinalTheorems.EffCartier (Z.comap O₂.ι) → FinalTheorems.Blowup π Z' := by sorry

alias «GlobalTheory».«CompanionTheory».«Hypotheses₂».«BlowupGlue».«blowup_of_eq_on_open» := P2M_GlobalTheory_CompanionTheory_Hypotheses__BlowupGlue_blowup_of_eq_on_open_2be0684b2feb
