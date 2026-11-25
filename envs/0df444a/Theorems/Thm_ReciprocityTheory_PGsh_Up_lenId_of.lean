-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_lenId_of
-- name    : ReciprocityTheory.PGsh.Up.lenId_of
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:08:39.034692+00:00
-- url     : https://prove2.me/theorems/005aef40-c4d8-48f2-9835-c91e57844211
-- title:
--   Up: len Id of
-- statement:
--   The Up construction uses the len Id of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/LenIdBStatement.lean#L164-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/LenIdBStatement.lean#L164-L174

import Definitions.Def_ReciprocityTheory_DualLattices_LenIdStatement
import Definitions.Def_ReciprocityTheory_DualLattices_MemOfSumSingleEqZero
import Definitions.Def_ReciprocityTheory_DualLattices_LenIdBStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
variable {R : Type} [CommRing R] {g m : ℕ}

theorem ReciprocityTheory.PGsh.Up.lenId_of
    (hS2 : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C],
      v.Integers R → ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (X : Matrix κ κ R),
      HasLen v R ((κ → R) ⧸ LinearMap.range X.mulVecLin) (v (algebraMap R C X.det)))
    (hB : LenIdBStatement) : LenIdStatement := by sorry
