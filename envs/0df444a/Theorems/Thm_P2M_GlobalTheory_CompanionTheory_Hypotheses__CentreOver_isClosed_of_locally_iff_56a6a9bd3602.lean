-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_isClosed_of_locally_iff_56a6a9bd3602
-- name    : P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_isClosed_of_locally_iff_56a6a9bd3602
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:04:59.651578+00:00
-- url     : https://prove2.me/theorems/4381eb7b-da2a-4149-958a-4eb151a56e1d
-- title:
--   P2 M Global Theory Companion Theory Hypotheses  Centre Over is Closed of locally iff 56a6a9bd3602: P2 M Global Theory Companion Theory Hypotheses  Centre Over is Closed of locally iff 56a6a9bd3602
-- statement:
--   The P2 M Global Theory Companion Theory Hypotheses  Centre Over is Closed of locally iff 56a6a9bd3602 construction uses the P2 M Global Theory Companion Theory Hypotheses  Centre Over is Closed of locally iff 56a6a9bd3602 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/IsClosedCartierLocusSupport.lean#L65-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/IsClosedCartierLocusSupport.lean#L65-L73

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

theorem P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_isClosed_of_locally_iff_56a6a9bd3602 {T : Type*} [TopologicalSpace T] {C : Set T} (hC : IsClosed C)
    (P : T → Prop) (h : ∀ x ∈ C, ∃ V : Set T, IsOpen V ∧ x ∈ V ∧ ∀ y ∈ V, y ∈ C → (P y ↔ P x)) :
    IsClosed {x | x ∈ C ∧ P x} := by sorry

alias «GlobalTheory».«CompanionTheory».«Hypotheses₂».«CentreOver».«isClosed_of_locally_iff» := P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_isClosed_of_locally_iff_56a6a9bd3602
