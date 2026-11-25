-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AntisymDivisible_vanish_of_open_4ef6119401a2
-- name    : P2M_GroundTheory_Heights__Heights_AntisymDivisible_vanish_of_open_4ef6119401a2
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:14:59.293472+00:00
-- url     : https://prove2.me/theorems/7cb17f71-170c-4516-90bb-3a0a014dffc0
-- title:
--   P2 M Ground Theory Heights  Heights Antisym Divisible vanish of open 4ef6119401a2: P2 M Ground Theory Heights  Heights Antisym Divisible vanish of open 4ef6119401a2
-- statement:
--   The P2 M Ground Theory Heights  Heights Antisym Divisible vanish of open 4ef6119401a2 construction uses the P2 M Ground Theory Heights  Heights Antisym Divisible vanish of open 4ef6119401a2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PAntisymDivisible.lean#L102-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PAntisymDivisible.lean#L102-L127

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PAntisymDivisible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
open GroundTheory.Heights₂.Heights.AntisymDivisible
variable {σ : Type*} [DecidableEq σ]

theorem P2M_GroundTheory_Heights__Heights_AntisymDivisible_vanish_of_open_4ef6119401a2 [Fintype σ] (u v : σ) (P : MvPolynomial σ ℝ) (O : Set (σ → ℝ))
    (hO : IsOpen O) (hne : (O ∩ {x | x u = x v}).Nonempty)
    (h : ∀ x ∈ O ∩ {x | x u = x v}, eval x P = 0) :
    ∀ x : σ → ℝ, x u = x v → eval x P = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AntisymDivisible».«vanish_of_open» := P2M_GroundTheory_Heights__Heights_AntisymDivisible_vanish_of_open_4ef6119401a2
