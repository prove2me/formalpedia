-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_cartAt_of_notMem_support_9dc6313038df
-- name    : P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_cartAt_of_notMem_support_9dc6313038df
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:04:17.214822+00:00
-- url     : https://prove2.me/theorems/cb5dc2f7-beb5-4e6b-99b8-cf5d86b6d660
-- title:
--   P2 M Global Theory Companion Theory Hypotheses  Centre Over cart At of not Mem support 9dc6313038df: P2 M Global Theory Companion Theory Hypotheses  Centre Over cart At of not Mem support 9dc6313038df
-- statement:
--   The P2 M Global Theory Companion Theory Hypotheses  Centre Over cart At of not Mem support 9dc6313038df construction uses the P2 M Global Theory Companion Theory Hypotheses  Centre Over cart At of not Mem support 9dc6313038df property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/CartierAtOfNotMemSupport.lean#L9-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/CartierAtOfNotMemSupport.lean#L9-L20

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_EffCartierIffForallCartAt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_CartierAtOfNotMemSupport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver

theorem P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_cartAt_of_notMem_support_9dc6313038df {X : Scheme.{0}} (J : X.IdealSheafData) (x : X) (hx : x ∉ J.support) :
    CartAt J x := by sorry

alias «GlobalTheory».«CompanionTheory».«Hypotheses₂».«CentreOver».«cartAt_of_notMem_support» := P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_cartAt_of_notMem_support_9dc6313038df
