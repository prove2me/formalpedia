-- Prove2me | Theorems.Thm_QECCertificates_LRAT_chainAssign_tail
-- name    : QECCertificates.LRAT.chainAssign_tail
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:58:41.30881+00:00
-- url     : https://prove2.me/theorems/8f648a82-b986-4168-9861-011fc1bd4244
-- title:
--   LRAT: chain Assign tail
-- statement:
--   Feeding the assignment of one segment of a chain on into its tail yields the same
--   assignment: the concatenation lemma.
--
--   Note that the two agree exactly at `t = c` (the left side takes the new accumulator
--   `acc ⊕ σ x`, the right side takes the value of `chainFill` at the counter), which is
--   precisely why `chainFill` does not read below the counter.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Complete.lean#L161-L176
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Complete.lean#L161-L176

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT

theorem QECCertificates.LRAT.chainAssign_tail (σ : Assign) (x : Nat) (rest : List Nat) (acc : Bool) (c : Nat)
    (hrest : ∀ t ∈ rest, t < c) :
    ∀ t, chainAssign (chainAssign σ (x :: rest) acc c) rest
          (chainAssign σ (x :: rest) acc c c) (c + 1) t
        = chainAssign σ (x :: rest) acc c t := by sorry
