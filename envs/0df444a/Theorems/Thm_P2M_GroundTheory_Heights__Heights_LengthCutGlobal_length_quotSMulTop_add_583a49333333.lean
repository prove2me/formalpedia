-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LengthCutGlobal_length_quotSMulTop_add_583a49333333
-- name    : P2M_GroundTheory_Heights__Heights_LengthCutGlobal_length_quotSMulTop_add_583a49333333
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:26:01.772246+00:00
-- url     : https://prove2.me/theorems/ef7a19e2-0555-4af1-b8ed-4280a79e679e
-- title:
--   P2 M Ground Theory Heights  Heights Length Cut Global length quot SMul Top add 583a49333333: P2 M Ground Theory Heights  Heights Length Cut Global length quot SMul Top add 583a49333333
-- statement:
--   The P2 M Ground Theory Heights  Heights Length Cut Global length quot SMul Top add 583a49333333 construction uses the P2 M Ground Theory Heights  Heights Length Cut Global length quot SMul Top add 583a49333333 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLengthCutGlobal.lean#L37-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLengthCutGlobal.lean#L37-L54

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLengthCutGlobal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLengthCutGlobal
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
open scoped Pointwise
universe u v
open GroundTheory.Heights₂.Heights.LengthCutGlobal
variable {C : Type u} [CommRing C] (P : Ideal C) [P.IsPrime]
omit [P.IsPrime]

theorem P2M_GroundTheory_Heights__Heights_LengthCutGlobal_length_quotSMulTop_add_583a49333333 (y : C) {N M Q : Type*} [AddCommGroup N] [Module C N]
    [AddCommGroup M] [Module C M] [AddCommGroup Q] [Module C Q] (f : N →ₗ[C] M) (g : M →ₗ[C] Q)
    (hf : Function.Injective f) (hg : Function.Surjective g) (H : Function.Exact f g)
    (hy : ∀ q : Q, y • q = 0 → q = 0) :
    Module.length C (QuotSMulTop y M) =
      Module.length C (QuotSMulTop y N) + Module.length C (QuotSMulTop y Q) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LengthCutGlobal».«length_quotSMulTop_add» := P2M_GroundTheory_Heights__Heights_LengthCutGlobal_length_quotSMulTop_add_583a49333333
