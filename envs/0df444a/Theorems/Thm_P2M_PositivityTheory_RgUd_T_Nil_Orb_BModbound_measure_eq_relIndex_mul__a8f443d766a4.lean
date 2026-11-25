-- Prove2me | Theorems.Thm_P2M_PositivityTheory_RgUd_T_Nil_Orb_BModbound_measure_eq_relIndex_mul__a8f443d766a4
-- name    : P2M_PositivityTheory_RgUd_T_Nil_Orb_BModbound_measure_eq_relIndex_mul__a8f443d766a4
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:57:12.123156+00:00
-- url     : https://prove2.me/theorems/2cc3acb6-eb94-4535-af5f-9a2c4f92e2fa
-- title:
--   P2 M Positivity Theory Rg Ud T Nil Orb BModbound measure eq rel Index mul  a8f443d766a4: P2 M Positivity Theory Rg Ud T Nil Orb BModbound measure eq rel Index mul  a8f443d766a4
-- statement:
--   The P2 M Positivity Theory Rg Ud T Nil Orb BModbound measure eq rel Index mul  a8f443d766a4 construction uses the P2 M Positivity Theory Rg Ud T Nil Orb BModbound measure eq rel Index mul  a8f443d766a4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/CompactOrbits/NilpotentOrbits/OrbitIntegrals/ModulusBounds/HaarMeasureGL.lean#L10-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/CompactOrbits/NilpotentOrbits/OrbitIntegrals/ModulusBounds/HaarMeasureGL.lean#L10-L56

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

theorem P2M_PositivityTheory_RgUd_T_Nil_Orb_BModbound_measure_eq_relIndex_mul__a8f443d766a4 (G : Type) [AddGroup G] [MeasurableSpace G] [MeasurableAdd G]
    (μ : MeasureTheory.Measure G) [μ.IsAddLeftInvariant] (H K : AddSubgroup G) (hHK : H ≤ K)
    (hH : MeasurableSet (H : Set G)) (hi : H.relIndex K ≠ 0) :
    μ (K : Set G) = (H.relIndex K : ENNReal) * μ (H : Set G) := by sorry

alias «PositivityTheory».«RgUd».«T».«Nil».«Orb».«BModbound».«measure_eq_relIndex_mul'» := P2M_PositivityTheory_RgUd_T_Nil_Orb_BModbound_measure_eq_relIndex_mul__a8f443d766a4
