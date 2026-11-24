-- Prove2me | Theorems.Thm_PositivityTheory_RgUd_T_Nil_Orb_BModbound_LaurentWeightBound_sum_prj
-- name    : PositivityTheory.RgUd.T.Nil.Orb.BModbound.LaurentWeightBound.sum_prj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:59:02.952867+00:00
-- url     : https://prove2.me/theorems/6011ab05-7377-44d1-8e48-6fb96078d637
-- title:
--   Laurent Weight Bound: sum prj
-- statement:
--   The Laurent Weight Bound construction uses the sum prj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/CompactOrbits/NilpotentOrbits/OrbitIntegrals/ModulusBounds/LaurentCoeffZero.lean#L86-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/CompactOrbits/NilpotentOrbits/OrbitIntegrals/ModulusBounds/LaurentCoeffZero.lean#L86-L93

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

theorem PositivityTheory.RgUd.T.Nil.Orb.BModbound.LaurentWeightBound.sum_prj (P : GL (Fin n) k) (w : Fin n → ℤ) (y : Fin n → k) :
    ∑ m ∈ Finset.univ.image w, prj P w m y = y := by sorry
