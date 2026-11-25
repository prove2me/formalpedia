-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_locPrincipal_of_cartAt_2a84a79b84c2
-- name    : P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_locPrincipal_of_cartAt_2a84a79b84c2
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:03:12.278451+00:00
-- url     : https://prove2.me/theorems/05bd070b-2ded-4956-ac3c-4c951699b083
-- title:
--   P2 M Global Theory Companion Theory Hypotheses  Centre Over loc Principal of cart At 2a84a79b84c2: P2 M Global Theory Companion Theory Hypotheses  Centre Over loc Principal of cart At 2a84a79b84c2
-- statement:
--   The P2 M Global Theory Companion Theory Hypotheses  Centre Over loc Principal of cart At 2a84a79b84c2 construction uses the P2 M Global Theory Companion Theory Hypotheses  Centre Over loc Principal of cart At 2a84a79b84c2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/LocallyPrincipalOfCartierAt.lean#L44-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/LocallyPrincipalOfCartierAt.lean#L44-L89

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_EffCartierIffForallCartAt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocPrincipalSpan
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocallyPrincipalOfCartierAt
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
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver

theorem P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_locPrincipal_of_cartAt_2a84a79b84c2 : ∀ {X : Scheme.{0}} [IsIntegral X] (Z : X.IdealSheafData)
    (U : X.affineOpens) (q : PrimeSpectrum Γ(X, U.1)), CartAt Z (U.2.fromSpec q) →
    LocPrincipal (Z.ideal U) q.asIdeal := by sorry

alias «GlobalTheory».«CompanionTheory».«Hypotheses₂».«CentreOver».«locPrincipal_of_cartAt» := P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_locPrincipal_of_cartAt_2a84a79b84c2
