-- Prove2me | Theorems.Thm_PositivityTheory_RgUd_T_Nil_Orb_BModbound_LaurentWeightBound_gt_prj
-- name    : PositivityTheory.RgUd.T.Nil.Orb.BModbound.LaurentWeightBound.gt_prj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:59:01.433557+00:00
-- url     : https://prove2.me/theorems/bc8477f4-96af-448d-8844-b61e864b075d
-- title:
--   Laurent Weight Bound: gt prj
-- statement:
--   The Laurent Weight Bound construction uses the gt prj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/CompactOrbits/NilpotentOrbits/OrbitIntegrals/ModulusBounds/LaurentCoeffZero.lean#L95-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/CompactOrbits/NilpotentOrbits/OrbitIntegrals/ModulusBounds/LaurentCoeffZero.lean#L95-L103

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_OrbitIntegrals_ModulusBounds_LaurentCoeffZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Module Polynomial
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.Orb PositivityTheory.RgUd.T.Nil.Orb.BModbound
open PositivityTheory.RgUd.T.Nil.Orb.BModbound.LaurentWeightBound
variable {k : Type} [Field k] {n : ℕ}

theorem PositivityTheory.RgUd.T.Nil.Orb.BModbound.LaurentWeightBound.gt_prj (P : GL (Fin n) k) (w : Fin n → ℤ) (t : kˣ) (m : ℤ) (y : Fin n → k) :
    gt P w t *ᵥ prj P w m y = ((t ^ m : kˣ) : k) • prj P w m y := by sorry
