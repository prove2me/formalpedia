-- Prove2me | Theorems.Thm_PositivityTheory_RgJS_EulerProductLogLemmas_norm_lterm_le
-- name    : PositivityTheory.RgJS.EulerProductLogLemmas.norm_lterm_le
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:03:07.22536+00:00
-- url     : https://prove2.me/theorems/23abd730-b228-4061-8725-96b9433bb2d6
-- title:
--   Euler Product Log Lemmas: norm lterm le
-- statement:
--   The Euler Product Log Lemmas construction uses the norm lterm le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/JacquetShalikaBounds/AbsoluteRigidity/EulerLogarithms/EulerProductLogBound.lean#L80-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/JacquetShalikaBounds/AbsoluteRigidity/EulerLogarithms/EulerProductLogBound.lean#L80-L97

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_NewtonLow
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_EulerLogarithms_EulerProductLogBound
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
open PositivityTheory PositivityTheory.RgJS
open PositivityTheory.RgJS.EulerProductLogLemmas
variable {W : Type} {A B : Type} [Fintype A] [Fintype B]

theorem PositivityTheory.RgJS.EulerProductLogLemmas.norm_lterm_le {q : W → ℕ} {α : W → A → ℂ} {β : W → B → ℂ} {s : ℂ} (hq : ∀ w, 2 ≤ q w)
    (hα : ∀ w a, ‖α w a‖ ≤ Real.sqrt (q w)) (hβ : ∀ w b, ‖β w b‖ ≤ Real.sqrt (q w)) (p : W × ℕ) :
    ‖lterm q α β s p‖ ≤ maj q s (Fintype.card A * Fintype.card B) p := by sorry
