-- Prove2me | Theorems.Thm_P2M_FFactor_card_filter_congr__c7ce8e64b074
-- name    : P2M_FFactor_card_filter_congr__c7ce8e64b074
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:57:40.091247+00:00
-- url     : https://prove2.me/theorems/69062669-baad-40fa-8297-4ad83253a6e7
-- title:
--   P2 M FFactor card filter congr  c7ce8e64b074: P2 M FFactor card filter congr  c7ce8e64b074
-- statement:
--   Filters along equivalent predicates (with arbitrary decidability instances) have the same
--   cardinality.
--
--   Source: https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorCount.lean#L27-L29
-- source:
--   https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorCount.lean#L27-L29

module
public import Mathlib
public import Definitions.Def_FFactorLib_FFactorDefs
public import Definitions.Def_FFactorLib_FFactorSuff
public import Definitions.Def_FFactorLib_FFactorCount
set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph Classical
open FFactor
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {f : V → ℕ}
  {U : Set (GV G f)}

theorem P2M_FFactor_card_filter_congr__c7ce8e64b074 {α : Type*} [Fintype α] (p q : α → Prop) [DecidablePred p]
    [DecidablePred q] (h : ∀ a, p a ↔ q a) : #{a | p a} = #{a | q a} := by sorry

alias «FFactor».«card_filter_congr'» := P2M_FFactor_card_filter_congr__c7ce8e64b074
