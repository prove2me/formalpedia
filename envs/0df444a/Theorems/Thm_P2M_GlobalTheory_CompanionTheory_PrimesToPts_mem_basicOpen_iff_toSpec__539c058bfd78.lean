-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_PrimesToPts_mem_basicOpen_iff_toSpec__539c058bfd78
-- name    : P2M_GlobalTheory_CompanionTheory_PrimesToPts_mem_basicOpen_iff_toSpec__539c058bfd78
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:04:18.904806+00:00
-- url     : https://prove2.me/theorems/4d5ddce0-ad11-4d08-b39d-f782a079079d
-- title:
--   P2 M Global Theory Companion Theory Primes To Pts mem basic Open iff to Spec  539c058bfd78: P2 M Global Theory Companion Theory Primes To Pts mem basic Open iff to Spec  539c058bfd78
-- statement:
--   The P2 M Global Theory Companion Theory Primes To Pts mem basic Open iff to Spec  539c058bfd78 construction uses the P2 M Global Theory Companion Theory Primes To Pts mem basic Open iff to Spec  539c058bfd78 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/BasicOpenNormFibreIff.lean#L18-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/BasicOpenNormFibreIff.lean#L18-L21

import Mathlib
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Algebra__RegularHypothesesAndConclusion_0659ccbe52365dd5
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartId
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_FiniteFreeHom
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_BasicOpenNormFibreIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PrimesToPts

theorem P2M_GlobalTheory_CompanionTheory_PrimesToPts_mem_basicOpen_iff_toSpec__539c058bfd78 {X : Scheme.{0}} (f : Γ(X, ⊤)) (x : X) :
    x ∈ X.basicOpen f ↔ f ∉ (X.toSpecΓ x : PrimeSpectrum Γ(X, ⊤)).asIdeal := by sorry

alias «GlobalTheory».«CompanionTheory».«PrimesToPts».«mem_basicOpen_iff_toSpecΓ» := P2M_GlobalTheory_CompanionTheory_PrimesToPts_mem_basicOpen_iff_toSpec__539c058bfd78
