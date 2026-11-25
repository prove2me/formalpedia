-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_comp_mem_incidence_ad714cb5fc19
-- name    : P2M_GroundTheory_Heights__Heights_comp_mem_incidence_ad714cb5fc19
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:45:22.561713+00:00
-- url     : https://prove2.me/theorems/c613ee9e-484b-4c64-a325-7c476da33824
-- title:
--   P2 M Ground Theory Heights  Heights comp mem incidence ad714cb5fc19: P2 M Ground Theory Heights  Heights comp mem incidence ad714cb5fc19
-- statement:
--   The P2 M Ground Theory Heights  Heights comp mem incidence ad714cb5fc19 construction uses the P2 M Ground Theory Heights  Heights comp mem incidence ad714cb5fc19 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/RenameProdMapMul.lean#L15-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/RenameProdMapMul.lean#L15-L18

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_RenameProdMapMul
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
variable {F : Type*} [Field F] {n k : ℕ}

theorem P2M_GroundTheory_Heights__Heights_comp_mem_incidence_ad714cb5fc19 {I : Ideal (MvPolynomial (Fin n) F)} {u : Fin k × Fin n → AlgebraicClosure F}
    (hu : u ∈ incidence I k) (τ : Equiv.Perm (Fin k)) : u ∘ Prod.map τ id ∈ incidence I k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«comp_mem_incidence» := P2M_GroundTheory_Heights__Heights_comp_mem_incidence_ad714cb5fc19
