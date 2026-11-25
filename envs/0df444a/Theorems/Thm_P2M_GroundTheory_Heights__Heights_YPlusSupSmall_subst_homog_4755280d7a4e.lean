-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_YPlusSupSmall_subst_homog_4755280d7a4e
-- name    : P2M_GroundTheory_Heights__Heights_YPlusSupSmall_subst_homog_4755280d7a4e
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:44:10.896709+00:00
-- url     : https://prove2.me/theorems/21bc6f54-b24d-4034-be2b-a56d57de98aa
-- title:
--   P2 M Ground Theory Heights  Heights YPlus Sup Small subst homog 4755280d7a4e: P2 M Ground Theory Heights  Heights YPlus Sup Small subst homog 4755280d7a4e
-- statement:
--   The P2 M Ground Theory Heights  Heights YPlus Sup Small subst homog 4755280d7a4e construction uses the P2 M Ground Theory Heights  Heights YPlus Sup Small subst homog 4755280d7a4e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PYPlusSupSmall.lean#L50-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PYPlusSupSmall.lean#L50-L67

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PYPlusSupSmall
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
open GroundTheory.Heights₂.Heights.YPlusSupSmall
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {P : ArithVariety n} (D : AddBlockData P)

theorem P2M_GroundTheory_Heights__Heights_YPlusSupSmall_subst_homog_4755280d7a4e {τ : ℕ} {f : MvPolynomial (Coord D.extSizes) ℤ}
    (hf : Geo.IsMultiHomog (ι := blockIdx D.extSizes) f (Pi.single none τ))
    (G : Coord D.extSizes → MvPolynomial (Coord n) ℤ) (e : ι → ℕ)
    (hG : ∀ v, IsWeightedHomogeneous (coordDeg n) (G v) e) :
    IsWeightedHomogeneous (coordDeg n) (aeval G f) (τ • e) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«YPlusSupSmall».«subst_homog» := P2M_GroundTheory_Heights__Heights_YPlusSupSmall_subst_homog_4755280d7a4e
