-- Prove2me | Theorems.Thm_UlmsTheorem_isPSeparable_iff_iInf
-- name    : UlmsTheorem.isPSeparable_iff_iInf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:53:57.197408+00:00
-- url     : https://prove2.me/theorems/d9c4c732-bd7f-4829-9acc-536a256fc402
-- title:
--   Ulms Theorem: is PSeparable iff i Inf
-- statement:
--   `G` is `p`-separable iff `⋂_n p^n·G = 0`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/PGroups/Heights.lean#L61-L75
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/PGroups/Heights.lean#L61-L75

module
public import Mathlib.Data.ENat.Lattice
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_UlmSubgroups
public import Mathlib.Algebra.Module.NatInt
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_Heights
set_option autoImplicit true
@[expose] public section
public section
open UlmsTheorem
variable (p : ℕ)
variable {G : Type*} [AddCommGroup G]

theorem UlmsTheorem.isPSeparable_iff_iInf :
    IsPSeparable p G ↔ (⨅ n : ℕ, pPow p (G := G) n) = ⊥ := by sorry
