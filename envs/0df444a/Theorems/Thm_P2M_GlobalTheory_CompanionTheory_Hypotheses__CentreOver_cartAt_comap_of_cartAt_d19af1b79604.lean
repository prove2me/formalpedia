-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_cartAt_comap_of_cartAt_d19af1b79604
-- name    : P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_cartAt_comap_of_cartAt_d19af1b79604
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T14:43:21.055232+00:00
-- url     : https://prove2.me/theorems/427c6434-72bb-4d29-8381-64406480e7b7
-- title:
--   P2 M Global Theory Companion Theory Hypotheses  Centre Over cart At comap of cart At d19af1b79604: P2 M Global Theory Companion Theory Hypotheses  Centre Over cart At comap of cart At d19af1b79604
-- statement:
--   The P2 M Global Theory Companion Theory Hypotheses  Centre Over cart At comap of cart At d19af1b79604 construction uses the P2 M Global Theory Companion Theory Hypotheses  Centre Over cart At comap of cart At d19af1b79604 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/EffCartierRestrictIffCartierAt.lean#L33-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/EffCartierRestrictIffCartierAt.lean#L33-L85

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

theorem P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_cartAt_comap_of_cartAt_d19af1b79604 {X Y : Scheme.{0}} (J : Y.IdealSheafData) (f : X ⟶ Y)
    [IsOpenImmersion f] (x : X) (h : CartAt J (f x)) : CartAt (J.comap f) x := by sorry

alias «GlobalTheory».«CompanionTheory».«Hypotheses₂».«CentreOver».«cartAt_comap_of_cartAt» := P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_cartAt_comap_of_cartAt_d19af1b79604
