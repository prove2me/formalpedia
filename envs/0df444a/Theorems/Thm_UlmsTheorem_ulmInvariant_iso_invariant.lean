-- Prove2me | Theorems.Thm_UlmsTheorem_ulmInvariant_iso_invariant
-- name    : UlmsTheorem.ulmInvariant_iso_invariant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:58:05.110632+00:00
-- url     : https://prove2.me/theorems/56655e20-dfaa-439d-8915-f5013710abb1
-- title:
--   Ulms Theorem: ulm Invariant iso invariant
-- statement:
--   Isomorphic groups have equal Ulm invariants.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Invariance.lean#L177-L188
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Invariance.lean#L177-L188

module
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_UlmInvariants
public import Definitions.Def_LeanPool_UlmsTheorem_Ulm_Invariance
set_option autoImplicit true
@[expose] public section
public section
open UlmsTheorem
open Cardinal Ordinal
universe u
variable (p : ℕ) [hp : Fact p.Prime]

theorem UlmsTheorem.ulmInvariant_iso_invariant {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    (φ : G ≃+ H) (α : Ordinal) :
    ulmInvariant p α (G := G) = ulmInvariant p α (G := H) := by sorry
