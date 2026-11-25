-- Prove2me | Theorems.Thm_PositivityTheory_RgJS_EulerProductLogLemmas_x_nonneg
-- name    : PositivityTheory.RgJS.EulerProductLogLemmas.x_nonneg
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T09:02:34.439089+00:00
-- url     : https://prove2.me/theorems/265de968-08eb-4395-a12d-6deee83fb1f2
-- title:
--   Euler Product Log Lemmas: x nonneg
-- statement:
--   The Euler Product Log Lemmas construction uses the x nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/JacquetShalikaBounds/AbsoluteRigidity/EulerLogarithms/EulerProductLogBound.lean#L46-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/JacquetShalikaBounds/AbsoluteRigidity/EulerLogarithms/EulerProductLogBound.lean#L46-L46

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

theorem PositivityTheory.RgJS.EulerProductLogLemmas.x_nonneg {q : W → ℕ} (s : ℂ) (w : W) : 0 ≤ (q w : ℝ) ^ (1 - s.re) := by sorry
