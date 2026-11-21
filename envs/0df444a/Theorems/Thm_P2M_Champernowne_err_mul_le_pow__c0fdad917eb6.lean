-- Prove2me | Theorems.Thm_P2M_Champernowne_err_mul_le_pow__c0fdad917eb6
-- name    : P2M_Champernowne_err_mul_le_pow__c0fdad917eb6
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:39:18.649481+00:00
-- url     : https://prove2.me/theorems/33b81aae-2d24-426b-95e5-d8a2cba0344c
-- title:
--   P2 M Champernowne err mul le pow  c0fdad917eb6: P2 M Champernowne err mul le pow  c0fdad917eb6
-- statement:
--   Subtraction-free form for `M ≥ 2`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/Asymptotics.lean#L131-L146
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/Asymptotics.lean#L131-L146

module
public import Definitions.Def_LeanPool_Champernowne_Positions
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.SpecificLimits.Basic
public import Definitions.Def_LeanPool_Champernowne_Asymptotics
set_option autoImplicit true
@[expose] public section
public section
open Champernowne
open Filter Asymptotics Topology

theorem P2M_Champernowne_err_mul_le_pow__c0fdad917eb6 {b : ℕ} (hb : 1 < b) (n : ℕ) (w : List ℕ) (h2 : 2 ≤ champM b n) :
    7 * (w.length + 1) * b ^ (2 * w.length) * b ^ champM b n * ((b - 1) * champM b n)
      ≤ 2 * (7 * (w.length + 1) * b ^ (2 * w.length) * b ^ 2) * n := by sorry

alias «Champernowne».«err_mul_le_pow'» := P2M_Champernowne_err_mul_le_pow__c0fdad917eb6
