-- Prove2me | Theorems.Thm_QECCertificates_length_le_finrank_spanL_of_certificate
-- name    : QECCertificates.length_le_finrank_spanL_of_certificate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:12:16.67713+00:00
-- url     : https://prove2.me/theorems/d79837cc-b2c8-4b81-b8f3-761283107d3d
-- title:
--   QECCertificates: length le finrank span L of certificate
-- statement:
--   **A rank lower bound from a certificate**: if every row of `D` lies in `spanL L` and
--   `D` satisfies the echelon invariants, then `D.length ≤ dim spanL L`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RankEchelon.lean#L557-L572
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RankEchelon.lean#L557-L572

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankEchelon
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.length_le_finrank_spanL_of_certificate {L : List (Vec n)} {D : List (PivRow n)}
    (hsub : ∀ i : Fin D.length, (D.get i).1 ∈ spanL L)
    (h1 : EchSelf D) (h2 : EchPair D) :
    D.length ≤ Module.finrank (ZMod 2) (spanL L) := by sorry
