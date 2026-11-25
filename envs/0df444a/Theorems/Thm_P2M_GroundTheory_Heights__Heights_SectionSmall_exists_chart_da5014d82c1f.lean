-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionSmall_exists_chart_da5014d82c1f
-- name    : P2M_GroundTheory_Heights__Heights_SectionSmall_exists_chart_da5014d82c1f
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:37:58.725567+00:00
-- url     : https://prove2.me/theorems/69d07ada-617c-408f-8d6a-c3a1eed1b32c
-- title:
--   P2 M Ground Theory Heights  Heights Section Small exists chart da5014d82c1f: P2 M Ground Theory Heights  Heights Section Small exists chart da5014d82c1f
-- statement:
--   The P2 M Ground Theory Heights  Heights Section Small exists chart da5014d82c1f construction uses the P2 M Ground Theory Heights  Heights Section Small exists chart da5014d82c1f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PSectionSmall.lean#L44-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PSectionSmall.lean#L44-L48

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PSectionSmall
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ArithVariety_exists_chart_5599c818fd08
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_chart_3cad6f9af78e

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
open MvPolynomial
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
open GroundTheory.Heights₂.Heights.SectionSmall
omit [Fintype ι]

theorem P2M_GroundTheory_Heights__Heights_SectionSmall_exists_chart_da5014d82c1f {P : ArithVariety n} {z : Cone n ℂ} (hz : z ∈ P.points ℂ) :
    ∃ c : (k : ι) → Fin (n k + 1), ∀ k, z k (c k) ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SectionSmall».«exists_chart» := P2M_GroundTheory_Heights__Heights_SectionSmall_exists_chart_da5014d82c1f
