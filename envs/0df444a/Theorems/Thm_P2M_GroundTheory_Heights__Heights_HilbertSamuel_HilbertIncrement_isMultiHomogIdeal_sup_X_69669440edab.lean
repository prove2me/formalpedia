-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_HilbertIncrement_isMultiHomogIdeal_sup_X_69669440edab
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_HilbertIncrement_isMultiHomogIdeal_sup_X_69669440edab
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:19:24.685249+00:00
-- url     : https://prove2.me/theorems/67fc7731-8bba-43b6-942c-274621b88c78
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Hilbert Increment is Multi Homog Ideal sup X 69669440edab: P2 M Ground Theory Heights  Heights Hilbert Samuel Hilbert Increment is Multi Homog Ideal
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Hilbert Increment is Multi Homog Ideal sup X 69669440edab construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Hilbert Increment is Multi Homog Ideal sup X 69669440edab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PHilbertIncrement.lean#L87-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PHilbertIncrement.lean#L87-L99

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsHilbert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ColonSpanSingletonEqOfNotMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PHilbExactDivide
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PHilbertIncrement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.HilbertSamuel.HilbertIncrement
variable {K : Type} [DecidableEq K] {ι : K → Type} {F : Type u} [Field F]

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_HilbertIncrement_isMultiHomogIdeal_sup_X_69669440edab {q : Ideal (MRing ι F)} (hq : IsMultiHomogIdeal q)
    (v : Σ k, ι k) : IsMultiHomogIdeal (q ⊔ Ideal.span {(X v : MRing ι F)}) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«HilbertIncrement».«isMultiHomogIdeal_sup_X» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_HilbertIncrement_isMultiHomogIdeal_sup_X_69669440edab
