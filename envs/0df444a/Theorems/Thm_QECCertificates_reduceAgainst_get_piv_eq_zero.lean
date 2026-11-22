-- Prove2me | Theorems.Thm_QECCertificates_reduceAgainst_get_piv_eq_zero
-- name    : QECCertificates.reduceAgainst_get_piv_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:49:33.568873+00:00
-- url     : https://prove2.me/theorems/cf37f469-b543-451d-992d-fc0edb6e7f29
-- title:
--   QECCertificates: reduce Against get piv eq zero
-- statement:
--   **The key step**: once the fold inside `reduceAgainst` has finished, the accumulator
--   is 0 on **every** pivot column of that state.
--
--   The induction separates the head row from the rest. For the remaining rows it uses the
--   induction hypothesis, which holds for an arbitrary starting vector; for the pivot column of
--   the head row it uses the fact that the remaining rows are all 0 on that column, so the fold
--   does not change it, together with the starting vector already being zero there.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RankEchelon.lean#L182-L199
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RankEchelon.lean#L182-L199

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankEchelon
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.reduceAgainst_get_piv_eq_zero {D : List (PivRow n)} (v : Vec n) (h1 : EchSelf D)
    (h2 : EchPair D) : ∀ i : Fin D.length, (reduceAgainst D v) (D.get i).2 = 0 := by sorry
