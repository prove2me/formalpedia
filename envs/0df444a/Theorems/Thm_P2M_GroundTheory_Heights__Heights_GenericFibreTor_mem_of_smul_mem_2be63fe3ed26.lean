-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GenericFibreTor_mem_of_smul_mem_2be63fe3ed26
-- name    : P2M_GroundTheory_Heights__Heights_GenericFibreTor_mem_of_smul_mem_2be63fe3ed26
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:17:56.246153+00:00
-- url     : https://prove2.me/theorems/e5cc81bd-0cfb-4de1-9870-5b6caa3babeb
-- title:
--   P2 M Ground Theory Heights  Heights Generic Fibre Tor mem of smul mem 2be63fe3ed26: P2 M Ground Theory Heights  Heights Generic Fibre Tor mem of smul mem 2be63fe3ed26
-- statement:
--   The P2 M Ground Theory Heights  Heights Generic Fibre Tor mem of smul mem 2be63fe3ed26 construction uses the P2 M Ground Theory Heights  Heights Generic Fibre Tor mem of smul mem 2be63fe3ed26 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGenericFibreTor.lean#L12-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGenericFibreTor.lean#L12-L30

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericFibreTor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericFreeness
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGenericFibreTor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_GenericFibreTor_mem_of_smul_mem_2be63fe3ed26 {σ ι : Type*} (t : σ → ℂ)
    (L : Ideal (MvPolynomial ι (MvPolynomial σ ℂ))) {x : MvPolynomial ι (MvPolynomial σ ℂ)} (hx : x ∈ L)
    {u : MvPolynomial σ ℂ} (hu : eval t u ≠ 0)
    (h : u • x ∈ (RingHom.ker (eval t : MvPolynomial σ ℂ →+* ℂ)).map
      (C : MvPolynomial σ ℂ →+* MvPolynomial ι (MvPolynomial σ ℂ)) * L) :
    x ∈ (RingHom.ker (eval t : MvPolynomial σ ℂ →+* ℂ)).map
      (C : MvPolynomial σ ℂ →+* MvPolynomial ι (MvPolynomial σ ℂ)) * L := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GenericFibreTor».«mem_of_smul_mem» := P2M_GroundTheory_Heights__Heights_GenericFibreTor_mem_of_smul_mem_2be63fe3ed26
