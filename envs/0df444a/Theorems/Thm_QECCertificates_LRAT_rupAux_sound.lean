-- Prove2me | Theorems.Thm_QECCertificates_LRAT_rupAux_sound
-- name    : QECCertificates.LRAT.rupAux_sound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:57:49.726538+00:00
-- url     : https://prove2.me/theorems/84232567-3f4f-41be-b358-f68b0e6e9c18
-- title:
--   LRAT: rup Aux sound
-- statement:
--   **Soundness of RUP**: if propagation along the hints reaches a conflict, then any
--   assignment satisfying the clauses the hints point to satisfies `C`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/LRAT.lean#L280-L326
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/LRAT.lean#L280-L326

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

theorem QECCertificates.LRAT.rupAux_sound {K : Type} (D : ClauseDB K) {σ : Assign} {d : K} :
    ∀ (hints : List Nat) (a : PAssign), agrees σ a →
      (∀ h ∈ hints, ∀ E, D.get? d (h - 1) = some E → SatClause σ E) →
      rupAux D d a hints = true → False := by sorry
