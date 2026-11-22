-- Prove2me | Theorems.Thm_P2M_polychromNumber_subgroup__43cbba40acee
-- name    : P2M_polychromNumber_subgroup__43cbba40acee
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:44:14.372693+00:00
-- url     : https://prove2.me/theorems/4fd2378e-283a-44d1-8cc6-868c38b92d15
-- title:
--   P2 M polychrom Number subgroup  43cbba40acee: P2 M polychrom Number subgroup  43cbba40acee
-- statement:
--   The P2 M polychrom Number subgroup  43cbba40acee construction uses the P2 M polychrom Number subgroup  43cbba40acee property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/PolychromNumber.lean#L194-L198
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/PolychromNumber.lean#L194-L198

import Definitions.Def_Polychromatic_Colouring
import Definitions.Def_Polychromatic_PolychromNumber
import Theorems.Thm_hasPolychromColouring_neg
import Theorems.Thm_hasPolychromColouring_univ
attribute [local simp] hasPolychromColouring_neg
attribute [local simp] hasPolychromColouring_univ


set_option autoImplicit true
variable {G : Type*} [AddCommGroup G] {S : Finset G} {K : Type*}
open Finset Fintype Pointwise

theorem P2M_polychromNumber_subgroup__43cbba40acee (H : AddSubgroup G) {S : Finset G} (hSG : (S : Set G) ⊆ H) :
    polychromNumber (G := H) (S.preimage H.subtype (by simp)) = polychromNumber S := by sorry

alias «polychromNumber_subgroup'» := P2M_polychromNumber_subgroup__43cbba40acee
