-- Prove2me | Theorems.Thm_ReciprocityTheory_CA_RegGens_exists_regular_generators_maxIdeal
-- name    : ReciprocityTheory.CA.RegGens.exists_regular_generators_maxIdeal
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T09:38:32.125563+00:00
-- url     : https://prove2.me/theorems/74976d34-13e8-5176-9d35-1ba0fe2f77db
-- title:
--   Reg Gens: exists regular generators max Ideal
-- statement:
--   The Reg Gens construction uses the exists regular generators max Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/CohenMacaulay/RegGens.lean#L11-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/CohenMacaulay/RegGens.lean#L11-L80

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_RegGensA
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_RegGens
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Abelian IsLocalRing RingTheory.Sequence
universe u v
open ReciprocityTheory ReciprocityTheory.CA ReciprocityTheory.CA.RegGens
open Pointwise

theorem ReciprocityTheory.CA.RegGens.exists_regular_generators_maxIdeal : ∀ (d : ℕ) (P : Type u) [CommRing P] [IsRegularLocalRing P],
    ringKrullDim P = d →
    ∃ rs : List P, rs.length = d ∧ IsRegular P rs ∧ Ideal.ofList rs = maximalIdeal P := by sorry
