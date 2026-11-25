-- Prove2me | Theorems.Thm_PI_EmbPermWork_cj_eq
-- name    : PI.EmbPermWork.cj_eq
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:29:20.24679+00:00
-- url     : https://prove2.me/theorems/19c98aef-79a3-4dc2-b3d5-3bfa84c8f12f
-- title:
--   Emb Perm Work: cj eq
-- statement:
--   The Emb Perm Work construction uses the cj eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/EmbeddingPermutations/CjEq.lean#L6-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/EmbeddingPermutations/CjEq.lean#L6-L8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_EmbPerm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EmbeddingPermutations_CjEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.EmbPermWork

theorem PI.EmbPermWork.cj_eq (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (x : ℂ) (hx : x ∈ M) :
    PI.EmbPermDefs.cj M ρ x = ρ ⟨x, hx⟩ := by sorry
