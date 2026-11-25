-- Prove2me | Theorems.Thm_P2M_GlobalTheory_dot_self_nonneg__607dd4203c70
-- name    : P2M_GlobalTheory_dot_self_nonneg__607dd4203c70
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:12:06.97297+00:00
-- url     : https://prove2.me/theorems/f3273186-4fbe-4fba-8a35-5de8797d3d22
-- title:
--   P2 M Global Theory dot self nonneg  607dd4203c70: P2 M Global Theory dot self nonneg  607dd4203c70
-- statement:
--   The P2 M Global Theory dot self nonneg  607dd4203c70 construction uses the P2 M Global Theory dot self nonneg  607dd4203c70 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/SchurComplementBlockQuadraticLowerBound.lean#L39-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/SchurComplementBlockQuadraticLowerBound.lean#L39-L40

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_SchurComplementBlockQuadraticLowerBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexOrder
open GlobalTheory

theorem P2M_GlobalTheory_dot_self_nonneg__607dd4203c70 (n : ℕ) (x : Fin n → ℝ) : 0 ≤ x ⬝ᵥ x := by sorry

alias «GlobalTheory».«dot_self_nonneg'» := P2M_GlobalTheory_dot_self_nonneg__607dd4203c70
