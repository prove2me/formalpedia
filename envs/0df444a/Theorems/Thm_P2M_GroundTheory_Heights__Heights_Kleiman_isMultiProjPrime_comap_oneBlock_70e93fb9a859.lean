-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_isMultiProjPrime_comap_oneBlock_70e93fb9a859
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_isMultiProjPrime_comap_oneBlock_70e93fb9a859
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:24:15.253226+00:00
-- url     : https://prove2.me/theorems/a09f753d-0620-4ea4-aae2-22773b2b530b
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman is Multi Proj Prime comap one Block 70e93fb9a859: P2 M Ground Theory Heights  Heights Kleiman is Multi Proj Prime comap one Block 70e93fb9a859
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman is Multi Proj Prime comap one Block 70e93fb9a859 construction uses the P2 M Ground Theory Heights  Heights Kleiman is Multi Proj Prime comap one Block 70e93fb9a859 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PPointDegreePos.lean#L35-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PPointDegreePos.lean#L35-L71

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PointDegreePosSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PHilbertPositive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PCutRegular
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Assembly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PPointDegreePos
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
variable {k : Type u} [Field k] {N : ℕ}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_isMultiProjPrime_comap_oneBlock_70e93fb9a859 {Ω : Type w} [Field Ω] [Algebra k Ω] {x : Fin (N + 1) → Ω}
    {pp : Ideal (Poly k N)} (h : IsSubvar x pp 0) :
    NumbersDVR.IsMultiProjPrime (pp.comap (oneBlock (S := k) (N := N)).toRingHom) ∧
      FieldNumbers.relDim (pp.comap (oneBlock (S := k) (N := N)).toRingHom) =
        ((0 : ℕ) : WithBot (WithTop ℤ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«isMultiProjPrime_comap_oneBlock» := P2M_GroundTheory_Heights__Heights_Kleiman_isMultiProjPrime_comap_oneBlock_70e93fb9a859
