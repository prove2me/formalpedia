-- Prove2me | Theorems.Thm_QECCertificates_LRAT_no_light_logical_of_unsat
-- name    : QECCertificates.LRAT.no_light_logical_of_unsat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:01:21.566208+00:00
-- url     : https://prove2.me/theorems/db3bd65e-42cf-4b37-b4e6-cb53f8bf4123
-- title:
--   LRAT: no light logical of unsat
-- statement:
--   **The certificate is the lower bound (general form)**: if the formula produced by the encoder at
--   `(Rker, Rpair, n, k)` is unsatisfiable, then the corresponding code has no logical operator of
--   weight $\le k$.
--
--   The row-correspondence, index bounds and duplicate-free hypotheses connect the Boolean
--   encoder inputs to the matrix model. No solver output is assumed sound.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Distance.lean#L257-L318
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Distance.lean#L257-L318

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCleaning
public import Definitions.Def_LeanPool_QECCertificates_GF2_Witness
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Distance
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT

theorem QECCertificates.LRAT.no_light_logical_of_unsat {n k : ℕ} {Rker Rpair : List (List Nat)}
    {m₁ m₂ : ℕ} (M₁ : Matrix (Fin m₁) (Fin n) (ZMod 2))
    (M₂ : Matrix (Fin m₂) (Fin n) (ZMod 2)) {F : CNF}
    (hF : buildPair Rker Rpair n k = F) (hunsat : ¬ Satisfiable F) (hn : 0 < n)
    (hne₁ : ∀ r ∈ Rker, r ≠ []) (hne₂ : ∀ r ∈ Rpair, r ≠ [])
    (hb₁ : ∀ r ∈ Rker, ∀ t ∈ r, t < n) (hb₂ : ∀ r ∈ Rpair, ∀ t ∈ r, t < n)
    (hd₁ : ∀ r ∈ Rker, r.Nodup) (hd₂ : ∀ r ∈ Rpair, r.Nodup)
    (hrow₁ : Rker.map (rowOf n) = List.ofFn fun i => M₁ i)
    (hrow₂ : Rpair.map (rowOf n) = List.ofFn fun i => M₂ i) :
    ¬ ∃ E : Vec n, (support E).card ≤ k ∧ E ∈ (Matrix.toLin' M₁).ker
      ∧ E ∉ M₂.certificateRowSpace := by sorry
