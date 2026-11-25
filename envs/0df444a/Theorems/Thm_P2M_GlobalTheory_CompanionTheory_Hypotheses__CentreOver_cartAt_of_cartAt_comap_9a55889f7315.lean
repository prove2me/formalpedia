-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_cartAt_of_cartAt_comap_9a55889f7315
-- name    : P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_cartAt_of_cartAt_comap_9a55889f7315
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T14:51:32.050876+00:00
-- url     : https://prove2.me/theorems/129793f4-05d5-5cd4-a8c7-b990933f7441
-- title:
--   P2 M Global Theory Companion Theory Hypotheses  Centre Over cart At of cart At comap 9a55889f7315: P2 M Global Theory Companion Theory Hypotheses  Centre Over cart At of cart At comap 9a55889f7315
-- statement:
--   The P2 M Global Theory Companion Theory Hypotheses  Centre Over cart At of cart At comap 9a55889f7315 construction uses the P2 M Global Theory Companion Theory Hypotheses  Centre Over cart At of cart At comap 9a55889f7315 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/EffCartierRestrictIffCartierAt.lean#L13-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/EffCartierRestrictIffCartierAt.lean#L13-L24

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

theorem P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_cartAt_of_cartAt_comap_9a55889f7315 {X Y : Scheme.{0}} (J : Y.IdealSheafData) (f : X ⟶ Y)
    [IsOpenImmersion f] (x : X) (h : CartAt (J.comap f) x) : CartAt J (f x) := by sorry

alias «GlobalTheory».«CompanionTheory».«Hypotheses₂».«CentreOver».«cartAt_of_cartAt_comap» := P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_cartAt_of_cartAt_comap_9a55889f7315
