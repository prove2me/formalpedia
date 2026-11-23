-- Prove2me | Theorems.Thm_PositivityTheory_RgJS_EulerProductLogLemmas_lterm_eq
-- name    : PositivityTheory.RgJS.EulerProductLogLemmas.lterm_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:08:15.860242+00:00
-- url     : https://prove2.me/theorems/833dd338-945f-402e-bc73-abcd67797333
-- title:
--   Euler Product Log Lemmas: lterm eq
-- statement:
--   The Euler Product Log Lemmas construction uses the lterm eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/JacquetShalikaBounds/AbsoluteRigidity/EulerLogarithms/EulerProductLogBound.lean#L16-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/JacquetShalikaBounds/AbsoluteRigidity/EulerLogarithms/EulerProductLogBound.lean#L16-L23

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

theorem PositivityTheory.RgJS.EulerProductLogLemmas.lterm_eq (q : W → ℕ) (α : W → A → ℂ) (β : W → B → ℂ) (s : ℂ) (p : W × ℕ) :
    lterm q α β s p = ∑ a, ∑ b, zz q α β s p.1 a b ^ (p.2 + 1) / ((p.2 : ℂ) + 1) := by sorry
