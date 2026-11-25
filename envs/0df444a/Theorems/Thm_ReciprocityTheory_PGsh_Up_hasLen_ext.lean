-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_hasLen_ext
-- name    : ReciprocityTheory.PGsh.Up.hasLen_ext
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:28:08.15222+00:00
-- url     : https://prove2.me/theorems/f26283c5-0370-4009-b70d-de91d6cfc90c
-- title:
--   Up: has Len ext
-- statement:
--   The Up construction uses the has Len ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/MemOfSumSingleEqZero.lean#L39-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/MemOfSumSingleEqZero.lean#L39-L190

import Definitions.Def_ReciprocityTheory_DualLattices_ProdDvdOfIso
import Definitions.Def_ReciprocityTheory_DualLattices_MemOfSumSingleEqZero
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

theorem ReciprocityTheory.PGsh.Up.hasLen_ext {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R]
    [Algebra R C]
    (hS2 : ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (X : Matrix κ κ R),
      HasLen v R ((κ → R) ⧸ LinearMap.range X.mulVecLin) (v (algebraMap R C X.det)))
    {A B D : Type} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [AddCommGroup D]
    [Module R D] (ι : A →ₗ[R] B) (π : B →ₗ[R] D) (hι : Function.Injective ι)
    (hπ : Function.Surjective π) (hex : LinearMap.range ι = LinearMap.ker π) {a c : NNReal}
    (ha : HasLen v R A a) (hc : HasLen v R D c) : HasLen v R B (a * c) := by sorry
