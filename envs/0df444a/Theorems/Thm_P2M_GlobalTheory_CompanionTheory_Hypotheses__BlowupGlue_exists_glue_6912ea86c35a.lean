-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_Hypotheses__BlowupGlue_exists_glue_6912ea86c35a
-- name    : P2M_GlobalTheory_CompanionTheory_Hypotheses__BlowupGlue_exists_glue_6912ea86c35a
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T14:55:44.008863+00:00
-- url     : https://prove2.me/theorems/e3931c4e-259a-5dbe-b868-2ad19856d61d
-- title:
--   P2 M Global Theory Companion Theory Hypotheses  Blowup Glue exists glue 6912ea86c35a: P2 M Global Theory Companion Theory Hypotheses  Blowup Glue exists glue 6912ea86c35a
-- statement:
--   The P2 M Global Theory Companion Theory Hypotheses  Blowup Glue exists glue 6912ea86c35a construction uses the P2 M Global Theory Companion Theory Hypotheses  Blowup Glue exists glue 6912ea86c35a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/BlowupOfAgreeingIdealCartier.lean#L49-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/BlowupOfAgreeingIdealCartier.lean#L49-L75

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

theorem P2M_GlobalTheory_CompanionTheory_Hypotheses__BlowupGlue_exists_glue_6912ea86c35a {W Y : Scheme.{0}} (W₁ W₂ : W.Opens) (h : W₁ ⊔ W₂ = ⊤) (σ₁ : W₁.toScheme ⟶ Y)
    (σ₂ : W₂.toScheme ⟶ Y)
    (hc : ∀ (T : Scheme.{0}) (a : T ⟶ W₁) (b : T ⟶ W₂) [IsOpenImmersion a], a ≫ W₁.ι = b ≫ W₂.ι →
      a ≫ σ₁ = b ≫ σ₂) :
    ∃ s : W ⟶ Y, W₁.ι ≫ s = σ₁ ∧ W₂.ι ≫ s = σ₂ := by sorry

alias «GlobalTheory».«CompanionTheory».«Hypotheses₂».«BlowupGlue».«exists_glue» := P2M_GlobalTheory_CompanionTheory_Hypotheses__BlowupGlue_exists_glue_6912ea86c35a
