-- Prove2me | Theorems.Thm_P2M_MatchingLogic_semantic_localization_of_closed___79ca4e008704
-- name    : P2M_MatchingLogic_semantic_localization_of_closed___79ca4e008704
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:18:52.468662+00:00
-- url     : https://prove2.me/theorems/2dcd1897-e5e4-4408-8fc4-219c28b6ff4f
-- title:
--   P2 M Matching Logic semantic localization of closed   79ca4e008704: P2 M Matching Logic semantic localization of closed   79ca4e008704
-- statement:
--   **Theorem 13 (semantic localization).**  `Γ ⊨ φ ↔ Δ_Γ ⊨loc φ`.
--
--   `(⇐)` is Lemma 7.  `(⇒)` is contrapositive: a local countermodel gives a point
--   `w` with `w ∈ ⟦Δ_Γ⟧` and `w ∉ ⟦φ⟧`; take `C := ⇝*[w]`, which is backward
--   closed, contains `w`, and satisfies `C ⊆ ⟦Γ⟧` by Lemma 8.  If `C = M` we are
--   done; otherwise the double cover `N` of Definition 10 satisfies `Γ` and refutes
--   `φ`, by Corollary 12.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Composite.lean#L82-L147
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Composite.lean#L82-L147

module
public import Definitions.Def_LeanPool_MatchingLogic_DoubleCover
public import Definitions.Def_LeanPool_MatchingLogic_Localization
public import Definitions.Def_LeanPool_MatchingLogic_Locality
public import Definitions.Def_LeanPool_MatchingLogic_Composite
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]

theorem P2M_MatchingLogic_semantic_localization_of_closed___79ca4e008704 {Γ : Set (Pattern S Var)}
    {φ : Pattern S Var} (hΓ : ∀ γ ∈ Γ, Closed γ) :
    GlobalCons Γ φ ↔ LocalCons (localize Γ) φ := by sorry

alias «MatchingLogic».«semantic_localization_of_closed_Γ» := P2M_MatchingLogic_semantic_localization_of_closed___79ca4e008704
