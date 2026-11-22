-- Prove2me | Theorems.Thm_QECCertificates_linearIndependent_get_of_echelon
-- name    : QECCertificates.linearIndependent_get_of_echelon
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:49:37.89806+00:00
-- url     : https://prove2.me/theorems/42ffcd58-0807-467c-93e0-a6115430c556
-- title:
--   QECCertificates: linear Independent get of echelon
-- statement:
--   **The rows of an echelon form are linearly independent**.
--
--   Take the **least index `j` whose coefficient in the linear combination is nonzero** and
--   evaluate on the pivot column of row `j`: terms with index below `j` have coefficient 0, and
--   rows with index above `j` are 0 on that column by `EchPair`, so the combination takes the
--   value `g j ≠ 0` there, contradicting the combination being zero.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RankEchelon.lean#L209-L245
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RankEchelon.lean#L209-L245

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankEchelon
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.linearIndependent_get_of_echelon {D : List (PivRow n)} (h1 : EchSelf D) (h2 : EchPair D) :
    LinearIndependent (ZMod 2) (fun i : Fin D.length => (D.get i).1) := by sorry
