-- Prove2me | Theorems.Thm_QECCertificates_LRAT_buildPair_complete
-- name    : QECCertificates.LRAT.buildPair_complete
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:00:11.334346+00:00
-- url     : https://prove2.me/theorems/47c58531-6c8e-40ec-a9dc-67c1916c7d6d
-- title:
--   LRAT: build Pair complete
-- statement:
--   **Completeness of `buildPair`**: when the four semantic conditions hold, the encoding is
--   satisfiable — **with the witness pinned down on the input variables**.
--
--   Together with `buildPair_sat` of `Reflect/Encode.lean` (soundness) this composes into
--   **an equivalence with the Boolean semantic conditions**. `Reflect/Distance.lean` bridges
--   these conditions to binary matrices and Hamming weight. Composing that bridge with the
--   soundness theorem of `Reflect/LRAT.lean` gives a matrix-level distance lower bound.
--
--   The **agreement clause** `∀ t, t < 2 * n → τ t = σ t` is what an assembly needs and what a bare
--   "there exists a model" cannot supply: the base part is followed by other clause blocks, and to
--   carry a model of the base part past those blocks one has to know that the base model reads the
--   **input** variables — that is, the ones a lexicographic comparator compares — exactly as the
--   semantic data does. It costs nothing here, since the whole proof is already built out of
--   extensions that agree below their own starting point: the first segment agrees below `2 * n`, and
--   every later segment agrees with the previous one below a number that is at least `2 * n`
--   (`hge1`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Complete.lean#L1057-L1179
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Complete.lean#L1057-L1179

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT

theorem QECCertificates.LRAT.buildPair_complete {Rker Rpair : List (List Nat)} {n k : Nat} {σ : Assign}
    (hn : 0 < n) (hne₁ : ∀ r ∈ Rker, r ≠ []) (hne₂ : ∀ r ∈ Rpair, r ≠ [])
    (hcol₁ : ∀ r ∈ Rker, ∀ t ∈ r, t < n) (hcol₂ : ∀ r ∈ Rpair, ∀ t ∈ r, t < n)
    (hwt : cntS σ (List.range n) ≤ k)
    (hker : ∀ r ∈ Rker, dotS σ r = false)
    (hpair : ∀ r ∈ Rpair, dotS (fun t => σ (n + t)) r = false)
    (hxw : dotS (fun t => σ t && σ (n + t)) (List.range n) = true) :
    ∃ τ : Assign, (∀ t, t < 2 * n → τ t = σ t) ∧
      SatFormula τ (buildPair Rker Rpair n k) := by sorry
