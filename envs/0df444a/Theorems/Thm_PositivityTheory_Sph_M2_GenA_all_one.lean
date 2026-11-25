-- Prove2me | Theorems.Thm_PositivityTheory_Sph_M2_GenA_all_one
-- name    : PositivityTheory.Sph.M2.GenA.all_one
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:56:21.882585+00:00
-- url     : https://prove2.me/theorems/e1e5b2b1-5138-585b-b794-30174e46afd5
-- title:
--   Gen A: all one
-- statement:
--   The Gen A construction uses the all one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SphericalLattices/DgPerm.lean#L85-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SphericalLattices/DgPerm.lean#L85-L104

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_SphericalLattices_DgPerm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.Sph PositivityTheory.Sph.M2 PositivityTheory.Sph.M2.GenA
open Matrix
variable {K : Type} [Field K] {n : Type} [Fintype n] [DecidableEq n]

theorem PositivityTheory.Sph.M2.GenA.all_one (ψ : GL n K →* ℝ) (hpos : ∀ g, 0 < ψ g) {w : K} (h0 : w ≠ 0) (h1 : 1 + w ≠ 0)
    (hsc : ∀ u : Kˣ, ψ (dg fun _ => u) = 1) (g : GL n K) : ψ g = 1 := by sorry
