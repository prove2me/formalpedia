-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_fromSpec_mem_basicOpen_iff_8be40fd86d42
-- name    : P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_fromSpec_mem_basicOpen_iff_8be40fd86d42
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:03:51.507093+00:00
-- url     : https://prove2.me/theorems/27c25e5e-4468-4744-89dc-9563b7392f77
-- title:
--   P2 M Global Theory Companion Theory Hypotheses  Centre Over from Spec mem basic Open iff 8be40fd86d42: P2 M Global Theory Companion Theory Hypotheses  Centre Over from Spec mem basic Open iff 8be40fd8
-- statement:
--   The P2 M Global Theory Companion Theory Hypotheses  Centre Over from Spec mem basic Open iff 8be40fd86d42 construction uses the P2 M Global Theory Companion Theory Hypotheses  Centre Over from Spec mem basic Open iff 8be40fd86d42 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/IsClosedCartierLocusSupport.lean#L58-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/IsClosedCartierLocusSupport.lean#L58-L63

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

theorem P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_fromSpec_mem_basicOpen_iff_8be40fd86d42 {X : Scheme.{0}} (U : X.affineOpens) (q : PrimeSpectrum Γ(X, U.1))
    (f : Γ(X, U.1)) : U.2.fromSpec q ∈ X.basicOpen f ↔ f ∉ q.asIdeal := by sorry

alias «GlobalTheory».«CompanionTheory».«Hypotheses₂».«CentreOver».«fromSpec_mem_basicOpen_iff» := P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_fromSpec_mem_basicOpen_iff_8be40fd86d42
