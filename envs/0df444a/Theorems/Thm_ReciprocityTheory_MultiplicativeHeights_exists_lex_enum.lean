-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_exists_lex_enum
-- name    : ReciprocityTheory.MultiplicativeHeights.exists_lex_enum
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:04:06.50707+00:00
-- url     : https://prove2.me/theorems/bb1c5926-bdce-5685-9c9a-1f0c0d818118
-- title:
--   Multiplicative Heights: exists lex enum
-- statement:
--   The Multiplicative Heights construction uses the exists lex enum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ExpTorusMeanLeL2OfLex.lean#L73-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ExpTorusMeanLeL2OfLex.lean#L73-L90

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_ExpTorusMeanLeL2OfLex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Finset

theorem ReciprocityTheory.MultiplicativeHeights.exists_lex_enum {ι : Type*} [LinearOrder ι] (S : Finset (ι →₀ ℕ)) :
    ∃ m : Fin S.card → (ι →₀ ℕ), (∀ k, m k ∈ S) ∧ Function.Injective m ∧
      ∀ j k, j < k → toLex (m k) < toLex (m j) := by sorry
