-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_eq_of_embForm_dvd_53e4b6a641c5
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_eq_of_embForm_dvd_53e4b6a641c5
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:43:07.50202+00:00
-- url     : https://prove2.me/theorems/e7a9f6ba-4d9c-4a7d-9ce2-4c4219b5b54a
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Norm Form Irreducible eq of emb Form dvd 53e4b6a641c5: P2 M Ground Theory Heights  Heights Vertical Norm Form Irreducible eq of emb Form dvd 53e4b6a641c5
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Norm Form Irreducible eq of emb Form dvd 53e4b6a641c5 construction uses the P2 M Ground Theory Heights  Heights Vertical Norm Form Irreducible eq of emb Form dvd 53e4b6a641c5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PNormFormIrreducible.lean#L211-L226
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PNormFormIrreducible.lean#L211-L226

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

theorem P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_eq_of_embForm_dvd_53e4b6a641c5 (hgen : Algebra.adjoin E (Set.range x) = ⊤)
    (ht : ∑ j, algebraMap E L (t j) * x j = 1) {σ τ : L →ₐ[E] K}
    (h : embForm σ x ∣ embForm τ x) : σ = τ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«NormFormIrreducible».«eq_of_embForm_dvd» := P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_eq_of_embForm_dvd_53e4b6a641c5
