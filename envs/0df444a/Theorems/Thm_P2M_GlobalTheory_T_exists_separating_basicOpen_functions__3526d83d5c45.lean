-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_exists_separating_basicOpen_functions__3526d83d5c45
-- name    : P2M_GlobalTheory_T_exists_separating_basicOpen_functions__3526d83d5c45
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:06:26.387635+00:00
-- url     : https://prove2.me/theorems/91e3135b-eb45-5211-9d1f-e79ea34de5d1
-- title:
--   P2 M Global Theory T exists separating basic Open functions  3526d83d5c45: P2 M Global Theory T exists separating basic Open functions  3526d83d5c45
-- statement:
--   The P2 M Global Theory T exists separating basic Open functions  3526d83d5c45 construction uses the P2 M Global Theory T exists separating basic Open functions  3526d83d5c45 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSeparatingBasicOpenFunctionsStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSeparatingBasicOpenFunctionsStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSeparatingBasicOpenFunctions
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSeparatingBasicOpenFunctionsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_exists_separating_basicOpen_functions__3526d83d5c45 : ∀ (X : Scheme.{0}) (U : X.Opens), IsAffineOpen U → ∀ (F : Finset X), (∀ a ∈ F, a ∈ U) → (∀ a ∈ F, ∀ b ∈ F, a ⤳ b → a = b) → ∀ W : X → X.Opens, (∀ a ∈ F, a ∈ W a) → ∃ f : X → Γ(X, U), ∀ a ∈ F, a ∈ X.basicOpen (f a) ∧ X.basicOpen (f a) ≤ W a ∧ ∀ b ∈ F, b ≠ a → b ∉ X.basicOpen (f a) := by sorry

alias «GlobalTheory».«T».«exists_separating_basicOpen_functions'» := P2M_GlobalTheory_T_exists_separating_basicOpen_functions__3526d83d5c45
