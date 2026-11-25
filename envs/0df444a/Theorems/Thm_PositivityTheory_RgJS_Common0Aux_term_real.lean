-- Prove2me | Theorems.Thm_PositivityTheory_RgJS_Common0Aux_term_real
-- name    : PositivityTheory.RgJS.Common0Aux.term_real
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:03:18.535384+00:00
-- url     : https://prove2.me/theorems/5c5f4f10-163d-4a24-867d-46035581d857
-- title:
--   Common0 Aux: term real
-- statement:
--   The Common0 Aux construction uses the term real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/JacquetShalikaBounds/AbsoluteRigidity/SubtypeIteSums/CommonOfLandauEuler.lean#L71-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/JacquetShalikaBounds/AbsoluteRigidity/SubtypeIteSums/CommonOfLandauEuler.lean#L71-L86

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

theorem PositivityTheory.RgJS.Common0Aux.term_real (q : W → ℕ) (hq : ∀ w, 2 ≤ q w) (A : ∀ x, W → Fin (d x) → ℂ) {ι : Type} [Fintype ι]
    (u : ι → X × ℝ) (σ : ℝ) (p : W × ℕ) :
    Pw q A u p.1 p.2 * conj (Pw q A u p.1 p.2) * ((q p.1 : ℂ) ^ (-(σ : ℂ))) ^ (p.2 + 1) / (p.2 + 1) =
      ((cc q A u p * Real.exp (-(ll q p * σ)) : ℝ) : ℂ) := by sorry
