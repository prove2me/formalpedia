-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P21_fullSeparabilityClassification
-- name    : QAlgorithms.Papers.Independent.Information100.P21.fullSeparabilityClassification
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:03:15.813349+00:00
-- url     : https://prove2.me/theorems/a5dee95c-393c-4828-81ff-cdb1d1a3fae0
-- title:
--   X.27 — Theorem X.27 (Universal equality for the fully separable free set). Delete all one-dimensional parties and let k be
-- statement:
--   Let $d_j$ be positive finite local dimensions and let $k$ count those greater than one. Relative to full separability,
--   $$[\forall\rho,\ R_s^{\mathrm{FS}}(\rho)=R_g^{\mathrm{FS}}(\rho)]\iff[k\le1\ \text{or}\ (k=2\text{ and both active dimensions are }2)].$$
--   Every other finite system contains a strict-separation state. Empty and one-active-party systems are included. This concerns exact single-copy values and asserts an existential gap in the other systems.
-- source:
--   The Minimal Dimension of Entangled -Noise Advantage, arXiv:2609.28367v1, PDF p. 30, X.27 — Theorem X.27 (Universal equality for the fully separable free set). Delete all one-dimensional parties and let k be

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Information100.P21

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arxiv:2609.28367v1, PDF p. 30, Theorem X.27 (Universal equality for the fully separable free set). Delete all one-dimensional parties and let k be. -/
theorem fullSeparabilityClassification {P : Type*} [Fintype P] (d : P → ℕ) (hd : ∀ j,0<d j) :
  let k := (Finset.univ.filter (fun j => 1<d j)).card
  ((∀ rho : Op (Config d), QAlgorithms.IsDensityMatrix rho → fsR d true rho=fsR d false rho) ↔
    k≤1 ∨ (k=2 ∧ ∀ j,1<d j → d j=2)) ∧
  (¬(k≤1 ∨ (k=2 ∧ ∀ j,1<d j → d j=2)) →
    ∃ rho : Op (Config d), QAlgorithms.IsDensityMatrix rho ∧ fsR d false rho<fsR d true rho) := by sorry

end QAlgorithms.Papers.Independent.Information100.P21

end
