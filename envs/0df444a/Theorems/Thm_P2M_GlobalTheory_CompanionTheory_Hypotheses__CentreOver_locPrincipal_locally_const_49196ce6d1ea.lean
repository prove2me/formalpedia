-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_locPrincipal_locally_const_49196ce6d1ea
-- name    : P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_locPrincipal_locally_const_49196ce6d1ea
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:03:52.707995+00:00
-- url     : https://prove2.me/theorems/354aad86-5aee-4646-83d2-913b5fe5f436
-- title:
--   P2 M Global Theory Companion Theory Hypotheses  Centre Over loc Principal locally const 49196ce6d1ea: P2 M Global Theory Companion Theory Hypotheses  Centre Over loc Principal locally const 49196ce6d1
-- statement:
--   The P2 M Global Theory Companion Theory Hypotheses  Centre Over loc Principal locally const 49196ce6d1ea construction uses the P2 M Global Theory Companion Theory Hypotheses  Centre Over loc Principal locally const 49196ce6d1ea property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/IsClosedCartierLocusSupport.lean#L17-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/IsClosedCartierLocusSupport.lean#L17-L56

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_EffCartierIffForallCartAt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocPrincipalSpan
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ConormalFiniteProjectiveOfSmoothStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocallyPrincipalOfConormalRankOneStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ConormalRankOneOfLocallyPrincipalStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocallyPrincipalOfCartierAtStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_CartierAtOfLocallyPrincipalStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ExistsSmoothAffinePresentationPairStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_IsClosedCartierLocusSupport
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

theorem P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_locPrincipal_locally_const_49196ce6d1ea {k A : Type} [Field k] [CommRing A] [IsDomain A] (φ : k →+* A) (I : Ideal A)
    (hφ : φ.Smooth) (hI : ((Ideal.Quotient.mk I).comp φ).Smooth) (p : PrimeSpectrum A)
    (hp : I ≤ p.asIdeal) :
    ∃ s, s ∉ p.asIdeal ∧ ∀ q : PrimeSpectrum A, s ∉ q.asIdeal → I ≤ q.asIdeal →
      (LocPrincipal I q.asIdeal ↔ LocPrincipal I p.asIdeal) := by sorry

alias «GlobalTheory».«CompanionTheory».«Hypotheses₂».«CentreOver».«locPrincipal_locally_const» := P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_locPrincipal_locally_const_49196ce6d1ea
