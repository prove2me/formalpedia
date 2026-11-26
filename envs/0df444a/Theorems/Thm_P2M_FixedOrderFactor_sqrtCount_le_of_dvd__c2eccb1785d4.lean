-- Prove2me | Theorems.Thm_P2M_FixedOrderFactor_sqrtCount_le_of_dvd__c2eccb1785d4
-- name    : P2M_FixedOrderFactor_sqrtCount_le_of_dvd__c2eccb1785d4
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:55:50.489418+00:00
-- url     : https://prove2.me/theorems/0960bd44-b07d-432e-a5ff-a458a9a70baa
-- title:
--   P2 M Fixed Order Factor sqrt Count le of dvd  c2eccb1785d4: P2 M Fixed Order Factor sqrt Count le of dvd  c2eccb1785d4
-- statement:
--   `β` is nondecreasing as `s` decreases along divisibility.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Bias.lean#L101-L107
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Bias.lean#L101-L107

module
public import Definitions.Def_FixedOrderFactor_Local
public import Definitions.Def_FixedOrderFactor_Bias
set_option autoImplicit true
@[expose] public section
public section
open Finset Real Complex
open FixedOrderFactor

theorem P2M_FixedOrderFactor_sqrtCount_le_of_dvd__c2eccb1785d4 (M a : ℕ) {s s' : ℕ} (h : s' ∣ s) :
    sqrtCount M a s ≤ sqrtCount M a s' := by sorry

alias «FixedOrderFactor».«sqrtCount_le_of_dvd'» := P2M_FixedOrderFactor_sqrtCount_le_of_dvd__c2eccb1785d4
