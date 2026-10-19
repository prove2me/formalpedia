-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P21_fixedCutClassification
-- name    : QAlgorithms.Papers.Independent.Information100.P21.fixedCutClassification
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:59:07.601148+00:00
-- url     : https://prove2.me/theorems/593e001b-7f74-4aea-91f3-048978d53474
-- title:
--   IX.21 — Corollary IX.21 (Complete finite-dimensional classification across a fixed cut). Let H =                         i=1 C
-- statement:
--   Let positive local dimensions $d_j$ describe a finite multipartite system, and fix a nonempty proper set of parties $S$. Set $d_S=\prod_{j\in S}d_j$ and $d_{\bar S}=\prod_{j\notin S}d_j$. Across this fixed cut,
--   $$[\forall\rho,\ R_s^{S|\bar S}(\rho)=R_g^{S|\bar S}(\rho)]\iff[\min(d_S,d_{\bar S})=1\ \text{or}\ (d_S,d_{\bar S})=(2,2)].$$
--   Every other effective dimension contains a strict-gap state. The grouped dependent-product basis canonically identifies the original tensor basis; entanglement within either side is allowed.
-- source:
--   The Minimal Dimension of Entangled -Noise Advantage, arXiv:2609.28367v1, PDF p. 27, IX.21 — Corollary IX.21 (Complete finite-dimensional classification across a fixed cut). Let H =                         i=1 C

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Information100.P21

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arxiv:2609.28367v1, PDF p. 27, Corollary IX.21 (Complete finite-dimensional classification across a fixed cut). Let H =                         i=1 C. -/
theorem fixedCutClassification {n : ℕ} (d : Fin n → ℕ) (hd : ∀ j, 0<d j)
  (S : Finset (Fin n)) (hne : S.Nonempty) (hproper : S≠Finset.univ) :
  let da := ∏ j ∈ S, d j
  let db := ∏ j ∈ Sᶜ, d j
  ((∀ rho : Op (Side d S × Side d Sᶜ), QAlgorithms.IsDensityMatrix rho → rs rho=rg rho) ↔
    min da db=1 ∨ (da=2 ∧ db=2)) ∧
  (¬(min da db=1 ∨ (da=2 ∧ db=2)) →
    ∃ rho : Op (Side d S × Side d Sᶜ), QAlgorithms.IsDensityMatrix rho ∧ rg rho<rs rho) := by sorry

end QAlgorithms.Papers.Independent.Information100.P21

end
