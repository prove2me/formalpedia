-- Prove2me | Theorems.Thm_PositivityTheory_RgUd_Form_U_Lift2_KerOpen_isOpen_ker
-- name    : PositivityTheory.RgUd.Form.U.Lift2.KerOpen.isOpen_ker
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:00:40.886145+00:00
-- url     : https://prove2.me/theorems/708bf680-4f56-482d-b43e-16ec9860915e
-- title:
--   Ker Open: is Open ker
-- statement:
--   The Ker Open construction uses the is Open ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/HermitianForms/UnitaryLattices/SmoothColumnLifts/KerOpen.lean#L7-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/HermitianForms/UnitaryLattices/SmoothColumnLifts/KerOpen.lean#L7-L44

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_HermitianForms_UnitaryLattices_SmoothColumnLifts_KerOpen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.Form PositivityTheory.RgUd.Form.U PositivityTheory.RgUd.Form.U.Lift2 PositivityTheory.RgUd.Form.U.Lift2.KerOpen
open Filter Topology

theorem PositivityTheory.RgUd.Form.U.Lift2.KerOpen.isOpen_ker {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (φ : AddChar k Circle) (hφ : Continuous φ) :
    IsOpen {x : k | φ x = 1} := by sorry
