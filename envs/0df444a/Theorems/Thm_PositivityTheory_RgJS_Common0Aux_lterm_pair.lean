-- Prove2me | Theorems.Thm_PositivityTheory_RgJS_Common0Aux_lterm_pair
-- name    : PositivityTheory.RgJS.Common0Aux.lterm_pair
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:03:09.269833+00:00
-- url     : https://prove2.me/theorems/e521573a-edfd-4648-9448-fe4164d382a9
-- title:
--   Common0 Aux: lterm pair
-- statement:
--   The Common0 Aux construction uses the lterm pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/JacquetShalikaBounds/AbsoluteRigidity/SubtypeIteSums/CommonOfLandauEuler.lean#L18-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/JacquetShalikaBounds/AbsoluteRigidity/SubtypeIteSums/CommonOfLandauEuler.lean#L18-L45

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_NewtonLow
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_SubtypeIteSums_CommonOfLandauEuler
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open Finset
open PositivityTheory PositivityTheory.RgJS PositivityTheory.RgJS.Common0Aux
variable {W X : Type} {d : X → ℕ}

theorem PositivityTheory.RgJS.Common0Aux.lterm_pair (q : W → ℕ) (hq : ∀ w, 2 ≤ q w) {α β : Type} [Fintype α] [Fintype β] (a : W → α → ℂ)
    (b : W → β → ℂ) (σ t t' : ℝ) (p : W × ℕ) :
    lterm q a b (((σ + t + t' : ℝ)) : ℂ) p =
      (∑ x, (a p.1 x * (q p.1 : ℂ) ^ (-(t : ℂ))) ^ (p.2 + 1)) *
        conj (∑ y, (b p.1 y * (q p.1 : ℂ) ^ (-(t' : ℂ))) ^ (p.2 + 1)) *
        ((q p.1 : ℂ) ^ (-(σ : ℂ))) ^ (p.2 + 1) / (p.2 + 1) := by sorry
