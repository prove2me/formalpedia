-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P22_binary_vertex_classification
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P22.binary_vertex_classification
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:17:50.22727+00:00
-- url     : https://prove2.me/theorems/40ba46c3-b4a4-4c12-a80c-b1be79ef6c73
-- title:
--   Exact binary no-signaling vertex classification
-- statement:
--   The vertices of the binary-input binary-output NS polytope are exactly the sixteen deterministic devices L_alpha,beta,gamma,sigma and eight PR-type devices B_r,s,t given in (321)-(322). The two displayed families have cardinalities 16 and 8; every deterministic member is local and every PR-type member is nonlocal.
-- source:
--   Limitations on device independent key secure against non signaling adversary via the squashed non-locality, arXiv:1903.12154v7, PDF p. 56, Equations (321)-(322) and cited classification [98]

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P22

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Intakethird100.P22

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Advance50.P47
  (Box IsCorrelation IsNoSignaling HasLocalModel correlationMixture prBox)

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

open QAlgorithms.Papers.Independent.Gap48.P25 (classicalMI)

/-- PDF p.56, cited classification [98]: exactly sixteen local deterministic
and eight nonlocal PR-type vertices. Both counts and both locality classes
are included, not merely membership of the supplied examples. -/
theorem binary_vertex_classification :
    (∀ p : Box Bool Bool Bool Bool, IsVertex p ↔
      (∃ alpha beta gamma sigma, p = deterministicBox alpha beta gamma sigma) ∨
      (∃ r s t, p = prVariant r s t)) ∧
    (Set.range (fun v : Bool × Bool × Bool × Bool =>
      deterministicBox v.1 v.2.1 v.2.2.1 v.2.2.2)).ncard = 16 ∧
    (Set.range (fun v : Bool × Bool × Bool => prVariant v.1 v.2.1 v.2.2)).ncard = 8 ∧
    (∀ alpha beta gamma sigma, HasLocalModel (deterministicBox alpha beta gamma sigma)) ∧
    (∀ r s t, ¬ HasLocalModel (prVariant r s t)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P22

end
