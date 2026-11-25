-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_cartAt_of_locPrincipal_47d661a47a8e
-- name    : P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_cartAt_of_locPrincipal_47d661a47a8e
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:07:02.700348+00:00
-- url     : https://prove2.me/theorems/34cca9e2-35a2-4f4f-92a4-a4989dc2d562
-- title:
--   P2 M Global Theory Companion Theory Hypotheses  Centre Over cart At of loc Principal 47d661a47a8e: P2 M Global Theory Companion Theory Hypotheses  Centre Over cart At of loc Principal 47d661a47a8e
-- statement:
--   The P2 M Global Theory Companion Theory Hypotheses  Centre Over cart At of loc Principal 47d661a47a8e construction uses the P2 M Global Theory Companion Theory Hypotheses  Centre Over cart At of loc Principal 47d661a47a8e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/CartierAtOfLocallyPrincipal.lean#L11-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/CartierAtOfLocallyPrincipal.lean#L11-L53

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_EffCartierIffForallCartAt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocPrincipalSpan
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_CartierAtOfLocallyPrincipal
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

theorem P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_cartAt_of_locPrincipal_47d661a47a8e : ∀ {X : Scheme.{0}} [IsIntegral X] (Z : X.IdealSheafData)
    (U : X.affineOpens) (q : PrimeSpectrum Γ(X, U.1)),
    LocPrincipal (Z.ideal U) q.asIdeal → CartAt Z (U.2.fromSpec q) := by sorry

alias «GlobalTheory».«CompanionTheory».«Hypotheses₂».«CentreOver».«cartAt_of_locPrincipal» := P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_cartAt_of_locPrincipal_47d661a47a8e
