-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GenericFibreModelTransport_eval__mem_closure_7f74352ff210
-- name    : P2M_GroundTheory_Heights__Heights_GenericFibreModelTransport_eval__mem_closure_7f74352ff210
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:17:47.748551+00:00
-- url     : https://prove2.me/theorems/0d5e7a37-bafc-4e26-b51c-a4d0c7f1ef49
-- title:
--   P2 M Ground Theory Heights  Heights Generic Fibre Model Transport eval  mem closure 7f74352ff210: P2 M Ground Theory Heights  Heights Generic Fibre Model Transport eval  mem closure 7f74352ff210
-- statement:
--   The P2 M Ground Theory Heights  Heights Generic Fibre Model Transport eval  mem closure 7f74352ff210 construction uses the P2 M Ground Theory Heights  Heights Generic Fibre Model Transport eval  mem closure 7f74352ff210 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/QuotientLiftInjective.lean#L37-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/QuotientLiftInjective.lean#L37-L42

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_QuotientLiftInjective
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
open GroundTheory.Heights₂.Heights.GenericFibreModelTransport
open MvPolynomial

theorem P2M_GroundTheory_Heights__Heights_GenericFibreModelTransport_eval__mem_closure_7f74352ff210 {σ F : Type*} [Field F] (c : ℤ →+* F) (y : σ → F) (f : MvPolynomial σ ℤ) :
    eval₂ c y f ∈ Subfield.closure (Set.range y) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GenericFibreModelTransport».«eval₂_mem_closure» := P2M_GroundTheory_Heights__Heights_GenericFibreModelTransport_eval__mem_closure_7f74352ff210
