-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocRingMem_algebraMap_mk_ne_zero_c9b8b026c1a2
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocRingMem_algebraMap_mk_ne_zero_c9b8b026c1a2
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:06:40.779837+00:00
-- url     : https://prove2.me/theorems/bc19a478-5e65-454e-afb1-37e808a60205
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Hom Loc Ring Mem algebra Map mk ne zero c9b8b026c1a2: P2 M Ground Theory Heights  Heights Numbers DVR Hom Loc Ring Mem algebra Map mk ne zero c9b8b026c1
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Hom Loc Ring Mem algebra Map mk ne zero c9b8b026c1a2 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Hom Loc Ring Mem algebra Map mk ne zero c9b8b026c1a2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PHomLocRingMem.lean#L11-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PHomLocRingMem.lean#L11-L15

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsHomLocRingLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PHomLocRingMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocRingMem_algebraMap_mk_ne_zero_c9b8b026c1a2 {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]
    (P : Ideal (MRing ι R)) [P.IsPrime] {g : MRing ι R} (hg : g ∉ P) :
    algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (Ideal.Quotient.mk P g) ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«HomLocRingMem».«algebraMap_mk_ne_zero» := P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocRingMem_algebraMap_mk_ne_zero_c9b8b026c1a2
