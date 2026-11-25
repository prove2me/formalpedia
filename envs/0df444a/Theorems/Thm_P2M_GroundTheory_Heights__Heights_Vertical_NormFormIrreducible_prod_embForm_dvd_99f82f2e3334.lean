-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_prod_embForm_dvd_99f82f2e3334
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_prod_embForm_dvd_99f82f2e3334
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:42:53.761482+00:00
-- url     : https://prove2.me/theorems/86270300-7685-4ef8-a8c7-ad9d2b1a74e5
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Norm Form Irreducible prod emb Form dvd 99f82f2e3334: P2 M Ground Theory Heights  Heights Vertical Norm Form Irreducible prod emb Form dvd 99f82f2e3334
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Norm Form Irreducible prod emb Form dvd 99f82f2e3334 construction uses the P2 M Ground Theory Heights  Heights Vertical Norm Form Irreducible prod emb Form dvd 99f82f2e3334 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PNormFormIrreducible.lean#L228-L245
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PNormFormIrreducible.lean#L228-L245

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsChowNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PNormFormIrreducible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial TensorProduct Matrix
noncomputable section
attribute [local instance] MvPolynomial.algebraMvPolynomial
open GroundTheory.Heights₂.Heights.Vertical.NormFormIrreducible
variable {E L K : Type*} [Field E] [Field L] [Field K] [Algebra E L] [Algebra E K] {n : ℕ}
  {x : Fin n → L} {t : Fin n → E}

theorem P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_prod_embForm_dvd_99f82f2e3334 [Fintype (L →ₐ[E] K)] (hgen : Algebra.adjoin E (Set.range x) = ⊤)
    (ht : ∑ j, algebraMap E L (t j) * x j = 1) {p : MvPolynomial (Fin n) K}
    (h : ∀ σ : L →ₐ[E] K, embForm σ x ∣ p) : ∏ σ : L →ₐ[E] K, embForm σ x ∣ p := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«NormFormIrreducible».«prod_embForm_dvd» := P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_prod_embForm_dvd_99f82f2e3334
