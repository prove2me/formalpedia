-- Prove2me | Theorems.Thm_PositivityTheory_RgUd_T_Nil_Orb_BModbound_LaurentWeightBound_laurent_coeff_zero
-- name    : PositivityTheory.RgUd.T.Nil.Orb.BModbound.LaurentWeightBound.laurent_coeff_zero
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T09:02:36.173035+00:00
-- url     : https://prove2.me/theorems/66b0c66e-74c1-40e3-9114-fb2eba80b037
-- title:
--   Laurent Weight Bound: laurent coeff zero
-- statement:
--   The Laurent Weight Bound construction uses the laurent coeff zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/CompactOrbits/NilpotentOrbits/OrbitIntegrals/ModulusBounds/LaurentCoeffZero.lean#L13-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/CompactOrbits/NilpotentOrbits/OrbitIntegrals/ModulusBounds/LaurentCoeffZero.lean#L13-L61

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

theorem PositivityTheory.RgUd.T.Nil.Orb.BModbound.LaurentWeightBound.laurent_coeff_zero [Infinite k] (M : Finset ℤ) (c : ℤ → k)
    (h : ∀ t : kˣ, ∑ m ∈ M, ((t ^ m : kˣ) : k) * c m = 0) : ∀ m ∈ M, c m = 0 := by sorry
