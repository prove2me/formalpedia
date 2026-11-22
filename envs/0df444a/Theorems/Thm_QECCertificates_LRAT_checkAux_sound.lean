-- Prove2me | Theorems.Thm_QECCertificates_LRAT_checkAux_sound
-- name    : QECCertificates.LRAT.checkAux_sound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:57:49.494579+00:00
-- url     : https://prove2.me/theorems/74357466-c3d4-44c1-9063-4f4961b00ba9
-- title:
--   LRAT: check Aux sound
-- statement:
--   **Soundness of the checker (the core)**: if `checkAux` returns true, then `σ` does
--   not satisfy the database.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/LRAT.lean#L361-L394
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/LRAT.lean#L361-L394

module
public import Mathlib.Data.List.Basic
public import Mathlib.Data.Nat.Basic
public import Std.Data.TreeMap.Lemmas
public import Std.Data.DTreeMap.Lemmas
public import Definitions.Def_LeanPool_QECCertificates_Reflect_LRAT
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT

theorem QECCertificates.LRAT.checkAux_sound {K : Type} (D : ClauseDB K) {σ : Assign} :
    ∀ (d : K) (steps : List LStep), (∀ C, D.Mem d C → SatClause σ C) →
      checkAux D d steps = true → False := by sorry
