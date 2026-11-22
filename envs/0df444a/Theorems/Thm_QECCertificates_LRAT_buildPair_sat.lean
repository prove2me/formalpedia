-- Prove2me | Theorems.Thm_QECCertificates_LRAT_buildPair_sat
-- name    : QECCertificates.LRAT.buildPair_sat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:15:18.715859+00:00
-- url     : https://prove2.me/theorems/49d69978-5782-4a5f-bd0a-469066b3053e
-- title:
--   LRAT: build Pair sat
-- statement:
--   **Encoding fidelity (the soundness direction)**: every satisfying assignment yields
--
--   * an `x` of weight at most `k` (`cntS` counts the true positions)
--   * `x` in the kernel of `Rker` and `w` in the kernel of `Rpair`
--   * `x.w = 1` (a pointwise conjunction followed by an XOR).
--
--   Together with `x.w = 1`, the third and fourth items make it impossible for `x` to lie in the
--   row space of `Rpair` (row space ⊆ (ker)⊥), that is, `x` is a **light logical operator**.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Encode.lean#L589-L621
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Encode.lean#L589-L621

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_LRAT
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT

theorem QECCertificates.LRAT.buildPair_sat {Rker Rpair : List (List Nat)} {n k : Nat} {σ : Assign}
    (hn : 0 < n) (hne₁ : ∀ r ∈ Rker, r ≠ []) (hne₂ : ∀ r ∈ Rpair, r ≠ [])
    (h : SatFormula σ (buildPair Rker Rpair n k)) :
    cntS σ (List.range n) ≤ k ∧
    (∀ r ∈ Rker, dotS σ r = false) ∧
    (∀ r ∈ Rpair, dotS (fun t => σ (n + t)) r = false) ∧
    dotS (fun t => σ t && σ (n + t)) (List.range n) = true := by sorry
