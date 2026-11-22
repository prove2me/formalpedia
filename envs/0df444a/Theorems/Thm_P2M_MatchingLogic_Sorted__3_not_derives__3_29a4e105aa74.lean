-- Prove2me | Theorems.Thm_P2M_MatchingLogic_Sorted__3_not_derives__3_29a4e105aa74
-- name    : P2M_MatchingLogic_Sorted__3_not_derives__3_29a4e105aa74
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:21:44.285684+00:00
-- url     : https://prove2.me/theorems/2956a813-2b47-4cfc-86ea-01b9b3611793
-- title:
--   P2 M Matching Logic Sorted  3 not derives  3 29a4e105aa74: P2 M Matching Logic Sorted  3 not derives  3 29a4e105aa74
-- statement:
--   **Proposition 30, third claim.**  `Γ ⊬ φ`.
--
--   `φ` has sort `c`, and `a` feeds only `a`, so any derivation of `φ` from `Γ`
--   would be a derivation from no hypotheses; soundness would then make `φ` valid,
--   and it is not — take `M_b = {r, s}` with `g_M(r) ≠ g_M(s)`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/SortedProof.lean#L264-L304
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/SortedProof.lean#L264-L304

module
public import Definitions.Def_LeanPool_MatchingLogic_Sorted
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Definitions.Def_LeanPool_MatchingLogic_EntryPoints
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Lattice.Image
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Lattice
public import Definitions.Def_LeanPool_MatchingLogic_SortedProof
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open MatchingLogic.Sorted
variable {S : MSignature} {Var : Type} [DecidableEq S.Srt] [DecidableEq Var]

theorem P2M_MatchingLogic_Sorted__3_not_derives__3_29a4e105aa74 (hS : MSoundness S3 Var) (x y : Var) (hxy : x ≠ y) :
    ¬ MProvable (Γ3 (Var := Var) x y) (φ3 (Var := Var) x y) := by sorry

alias «MatchingLogic».«Sorted».«Γ3_not_derives_φ3» := P2M_MatchingLogic_Sorted__3_not_derives__3_29a4e105aa74
