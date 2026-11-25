-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_isIsotropicLine_span_singleton_9971ad41966c
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_isIsotropicLine_span_singleton_9971ad41966c
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:40:03.122582+00:00
-- url     : https://prove2.me/theorems/4384010e-80ea-432c-81f6-7ed3e8c3a077
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume is Isotropic Line span singleton 9971ad41966c: P2 M Ground Theory Heights  Heights Finite Covolume is Isotropic Line span singleton 9971ad41966c
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume is Isotropic Line span singleton 9971ad41966c construction uses the P2 M Ground Theory Heights  Heights Finite Covolume is Isotropic Line span singleton 9971ad41966c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PLatticeOrbitsFinite.lean#L17-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PLatticeOrbitsFinite.lean#L17-L23

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PLatticeOrbitsFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module
open scoped Pointwise
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [NumberField F] [NumberField E] [IsTotallyReal F] [IsTotallyComplex E]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_isIsotropicLine_span_singleton_9971ad41966c (h : HermitianForm F E W) {x : W} (hx : x ≠ 0)
    (hxx : h.toSesq x x = 0) : IsIsotropicLine h (Submodule.span E {x}) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«isIsotropicLine_span_singleton» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_isIsotropicLine_span_singleton_9971ad41966c
