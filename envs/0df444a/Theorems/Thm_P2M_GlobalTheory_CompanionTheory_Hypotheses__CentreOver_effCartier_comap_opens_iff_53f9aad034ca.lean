-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_effCartier_comap_opens_iff_53f9aad034ca
-- name    : P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_effCartier_comap_opens_iff_53f9aad034ca
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T14:43:48.729723+00:00
-- url     : https://prove2.me/theorems/3bfc80a3-f6d2-40ee-970b-6cfae12e44de
-- title:
--   P2 M Global Theory Companion Theory Hypotheses  Centre Over eff Cartier comap opens iff 53f9aad034ca: P2 M Global Theory Companion Theory Hypotheses  Centre Over eff Cartier comap opens iff 53f9aad034
-- statement:
--   The P2 M Global Theory Companion Theory Hypotheses  Centre Over eff Cartier comap opens iff 53f9aad034ca construction uses the P2 M Global Theory Companion Theory Hypotheses  Centre Over eff Cartier comap opens iff 53f9aad034ca property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/EffCartierRestrictIffCartierAt.lean#L87-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/EffCartierRestrictIffCartierAt.lean#L87-L95

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_EffCartierIffForallCartAt
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WChartsB
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_EffCartierRestrictIffCartierAt
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver

theorem P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_effCartier_comap_opens_iff_53f9aad034ca : ∀ {X : Scheme.{0}} (J : X.IdealSheafData) (O : X.Opens),
    FinalTheorems.EffCartier (J.comap O.ι) ↔ ∀ x ∈ O, CartAt J x := by sorry

alias «GlobalTheory».«CompanionTheory».«Hypotheses₂».«CentreOver».«effCartier_comap_opens_iff» := P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_effCartier_comap_opens_iff_53f9aad034ca
