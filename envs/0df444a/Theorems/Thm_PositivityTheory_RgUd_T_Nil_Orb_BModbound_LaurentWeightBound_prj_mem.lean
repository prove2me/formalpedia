-- Prove2me | Theorems.Thm_PositivityTheory_RgUd_T_Nil_Orb_BModbound_LaurentWeightBound_prj_mem
-- name    : PositivityTheory.RgUd.T.Nil.Orb.BModbound.LaurentWeightBound.prj_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:58:51.695125+00:00
-- url     : https://prove2.me/theorems/758bbb4c-0617-4c99-82b8-30e4de681815
-- title:
--   Laurent Weight Bound: prj mem
-- statement:
--   The Laurent Weight Bound construction uses the prj mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/CompactOrbits/NilpotentOrbits/OrbitIntegrals/ModulusBounds/LaurentCoeffZero.lean#L113-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/CompactOrbits/NilpotentOrbits/OrbitIntegrals/ModulusBounds/LaurentCoeffZero.lean#L113-L139

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

theorem PositivityTheory.RgUd.T.Nil.Orb.BModbound.LaurentWeightBound.prj_mem [Infinite k] (P : GL (Fin n) k) (w : Fin n → ℤ) (W : Submodule k (Fin n → k))
    (hinv : ∀ t : kˣ, ∀ y ∈ W, gt P w t *ᵥ y ∈ W) (m : ℤ) (y : Fin n → k) (hy : y ∈ W) :
    prj P w m y ∈ W := by sorry
