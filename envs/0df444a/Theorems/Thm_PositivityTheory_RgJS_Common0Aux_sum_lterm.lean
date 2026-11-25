-- Prove2me | Theorems.Thm_PositivityTheory_RgJS_Common0Aux_sum_lterm
-- name    : PositivityTheory.RgJS.Common0Aux.sum_lterm
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:03:19.138074+00:00
-- url     : https://prove2.me/theorems/8edec0a9-bf79-42e3-87b8-7b7088f85d71
-- title:
--   Common0 Aux: sum lterm
-- statement:
--   The Common0 Aux construction uses the sum lterm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/JacquetShalikaBounds/AbsoluteRigidity/SubtypeIteSums/CommonOfLandauEuler.lean#L47-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/JacquetShalikaBounds/AbsoluteRigidity/SubtypeIteSums/CommonOfLandauEuler.lean#L47-L54

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

theorem PositivityTheory.RgJS.Common0Aux.sum_lterm (q : W → ℕ) (hq : ∀ w, 2 ≤ q w) (A : ∀ x, W → Fin (d x) → ℂ) {ι κ : Type} [Fintype ι] [Fintype κ]
    (u : ι → X × ℝ) (v : κ → X × ℝ) (σ : ℝ) (p : W × ℕ) :
    ∑ i, ∑ j, lterm q (A (u i).1) (A (v j).1) (((σ + (u i).2 + (v j).2 : ℝ)) : ℂ) p =
      Pw q A u p.1 p.2 * conj (Pw q A v p.1 p.2) * ((q p.1 : ℂ) ^ (-(σ : ℂ))) ^ (p.2 + 1) / (p.2 + 1) := by sorry
