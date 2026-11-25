-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartFinite_exists_pow_mem_b30bb039a736
-- name    : P2M_GroundTheory_Heights__Heights_ChartFinite_exists_pow_mem_b30bb039a736
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:35:04.321578+00:00
-- url     : https://prove2.me/theorems/74f058e5-cbcf-4417-9027-cb9eec980a99
-- title:
--   P2 M Ground Theory Heights  Heights Chart Finite exists pow mem b30bb039a736: P2 M Ground Theory Heights  Heights Chart Finite exists pow mem b30bb039a736
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Finite exists pow mem b30bb039a736 construction uses the P2 M Ground Theory Heights  Heights Chart Finite exists pow mem b30bb039a736 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartFinite.lean#L85-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartFinite.lean#L85-L153

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsSectionOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PFGNullstellensatz
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChowFormMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartFinite
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
open GroundTheory.Heights₂.Heights.ChartFinite
variable {F : Type} [Field F] {n e : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ChartFinite_exists_pow_mem_b30bb039a736 (I : Ideal (MvPolynomial (Fin n) F)) (f : MvPolynomial (Fin (e + 1) × Fin n) F)
    (t : Fin n → F) (hf : IsChowForm I (e + 1) f) (m : Fin n) :
    ∃ N : ℕ, (Polynomial.eval₂RingHom (rename (R := F) (Sum.inr : Fin e × Fin n → Fin n ⊕ Fin e × Fin n)).toRingHom
      (X (Sum.inl m)) (linePoly f t m)) ^ N ∈ chartIncIdeal I t e := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartFinite».«exists_pow_mem» := P2M_GroundTheory_Heights__Heights_ChartFinite_exists_pow_mem_b30bb039a736
