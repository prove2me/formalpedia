-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_PrimesToPts_comap_toSpec__ae60923711e0
-- name    : P2M_GlobalTheory_CompanionTheory_PrimesToPts_comap_toSpec__ae60923711e0
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:05:26.828879+00:00
-- url     : https://prove2.me/theorems/eaf5e5ef-9211-468b-9384-6943062f8bed
-- title:
--   P2 M Global Theory Companion Theory Primes To Pts comap to Spec  ae60923711e0: P2 M Global Theory Companion Theory Primes To Pts comap to Spec  ae60923711e0
-- statement:
--   The P2 M Global Theory Companion Theory Primes To Pts comap to Spec  ae60923711e0 construction uses the P2 M Global Theory Companion Theory Primes To Pts comap to Spec  ae60923711e0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/BasicOpenNormFibreIff.lean#L23-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/BasicOpenNormFibreIff.lean#L23-L29

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

theorem P2M_GlobalTheory_CompanionTheory_PrimesToPts_comap_toSpec__ae60923711e0 {P D : Scheme.{0}} (v : P ⟶ D) (z : P) :
    (P.toSpecΓ z : PrimeSpectrum Γ(P, ⊤)).asIdeal.comap v.appTop.hom =
      (D.toSpecΓ (v z) : PrimeSpectrum Γ(D, ⊤)).asIdeal := by sorry

alias «GlobalTheory».«CompanionTheory».«PrimesToPts».«comap_toSpecΓ» := P2M_GlobalTheory_CompanionTheory_PrimesToPts_comap_toSpec__ae60923711e0
