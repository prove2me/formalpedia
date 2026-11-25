-- Prove2me | Theorems.Thm_P2M_PositivityTheory_RgUd_T_Nil_Orb_BModbound_relIndex_ne_zero_of_isCompact_of_isOpen__ed8b7a4764f5
-- name    : P2M_PositivityTheory_RgUd_T_Nil_Orb_BModbound_relIndex_ne_zero_of_isCompact_of_isOpen__ed8b7a4764f5
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:06:29.772746+00:00
-- url     : https://prove2.me/theorems/ce816c9f-1b6e-5d1c-8d59-70a6db02c26d
-- title:
--   P2 M Positivity Theory Rg Ud T Nil Orb BModbound rel Index ne zero of is Compact of is Open  ed8b7a4764f5: P2 M Positivity Theory Rg Ud T Nil Orb BModbound rel Index ne zero of is Compact of is Open
-- statement:
--   The P2 M Positivity Theory Rg Ud T Nil Orb BModbound rel Index ne zero of is Compact of is Open  ed8b7a4764f5 construction uses the P2 M Positivity Theory Rg Ud T Nil Orb BModbound rel Index ne zero of is Compact of is Open  ed8b7a4764f5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/CompactOrbits/NilpotentOrbits/OrbitIntegrals/ModulusBounds/HaarMeasureGL.lean#L58-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/CompactOrbits/NilpotentOrbits/OrbitIntegrals/ModulusBounds/HaarMeasureGL.lean#L58-L66

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresModulus
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_OrbitIntegrals_ModulusBounds_HaarMeasureGL
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Module ValuativeRel MeasureTheory
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.Orb PositivityTheory.RgUd.T.Nil.Orb.BModbound

theorem P2M_PositivityTheory_RgUd_T_Nil_Orb_BModbound_relIndex_ne_zero_of_isCompact_of_isOpen__ed8b7a4764f5 {X : Type} [TopologicalSpace X] [AddCommGroup X]
    [IsTopologicalAddGroup X] (A H : AddSubgroup X) (hA : IsCompact (A : Set X)) (hH : IsOpen (H : Set X))
    (_hle : H ≤ A) : H.relIndex A ≠ 0 := by sorry

alias «PositivityTheory».«RgUd».«T».«Nil».«Orb».«BModbound».«relIndex_ne_zero_of_isCompact_of_isOpen'» := P2M_PositivityTheory_RgUd_T_Nil_Orb_BModbound_relIndex_ne_zero_of_isCompact_of_isOpen__ed8b7a4764f5
