-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_lift_self_77a0080631dc
-- name    : P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_lift_self_77a0080631dc
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:27:29.546798+00:00
-- url     : https://prove2.me/theorems/43c5738f-eb6a-4f86-a7ce-5aec28033b93
-- title:
--   P2 M Ground Theory Heights  Heights Inter Thm IExists lift self 77a0080631dc: P2 M Ground Theory Heights  Heights Inter Thm IExists lift self 77a0080631dc
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Thm IExists lift self 77a0080631dc construction uses the P2 M Ground Theory Heights  Heights Inter Thm IExists lift self 77a0080631dc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ThmIExistsFamily.lean#L113-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ThmIExistsFamily.lean#L113-L116

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsMultiHomogXpow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ThmIExistsFamily
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.ThmIExists
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_lift_self_77a0080631dc {n : ℕ} (J : Ideal (MRing ι) → (Fin n → HermLine ι) → ℝ) (W : Ideal (MRing ι))
    (L : Fin n → HermLine ι) : lift J W n L = J W L := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«ThmIExists».«lift_self» := P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_lift_self_77a0080631dc
