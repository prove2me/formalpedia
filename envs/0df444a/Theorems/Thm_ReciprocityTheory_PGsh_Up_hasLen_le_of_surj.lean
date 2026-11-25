-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_hasLen_le_of_surj
-- name    : ReciprocityTheory.PGsh.Up.hasLen_le_of_surj
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T17:19:43.014114+00:00
-- url     : https://prove2.me/theorems/7c2cc376-6e9f-4044-a519-2bc69f7e5f10
-- title:
--   Up: has Len le of surj
-- statement:
--   The Up construction uses the has Len le of surj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/HasLenLeOfSurj.lean#L15-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/HasLenLeOfSurj.lean#L15-L62

import Definitions.Def_ReciprocityTheory_DualLattices_LiftMonomialDeterminantStatement
import Definitions.Def_ReciprocityTheory_DualLattices_PowMemCarrier
import Definitions.Def_ReciprocityTheory_DualLattices_IsLocalOfIntegers
import Definitions.Def_ReciprocityTheory_DualLattices_MemOfSumSingleEqZero
import Definitions.Def_ReciprocityTheory_DualLattices_EigenLiftsFrobenius
import Definitions.Def_ReciprocityTheory_DualLattices_HasLenLeOfSurj
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
open ReciprocityTheory.PGsh.L2

theorem ReciprocityTheory.PGsh.Up.hasLen_le_of_surj {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R]
    [Algebra R C] (hv : v.Integers R) {M : Type} [AddCommGroup M] [Module R M] {z : NNReal}
    (hz : HasLen v R M z) (q : R) (r : ℕ)
    (π : M →ₗ[R] ((t : Fin r) → R ⧸ Ideal.span {q})) (hπ : Function.Surjective π) :
    z ≤ v (algebraMap R C q) ^ r := by sorry
