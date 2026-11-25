-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_classNum_pairDiff_mul_92ffd0efb78e
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_classNum_pairDiff_mul_92ffd0efb78e
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:09:21.172536+00:00
-- url     : https://prove2.me/theorems/431fb878-9791-4b3e-b47e-240f1357f451
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR class Num pair Diff mul 92ffd0efb78e: P2 M Ground Theory Heights  Heights Numbers DVR class Num pair Diff mul 92ffd0efb78e
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR class Num pair Diff mul 92ffd0efb78e construction uses the P2 M Ground Theory Heights  Heights Numbers DVR class Num pair Diff mul 92ffd0efb78e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairNumberExpansionIndependence.lean#L16-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairNumberExpansionIndependence.lean#L16-L38

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPairNumberExpansionKoszul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPairNumberExpansionIndependence
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
variable {K : Type*} [DecidableEq K] {ι : K → Type*}
  {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_classNum_pairDiff_mul_92ffd0efb78e {n e : ℕ} {W : Ideal (MRing ι O)}
    (hadd : ∀ (a₁ a₂ : K → ℤ) (l : List (K → ℤ)), e ≤ l.length →
      vNumL W ((a₁ + a₂) :: l) = vNumL W (a₁ :: l) + vNumL W (a₂ :: l))
    (z z' : Fin n → K → ℤ) (j : Fin n) {H : MvPolynomial (Fin n ⊕ Fin n) ℤ} {t : ℕ}
    (hH : H.IsHomogeneous t) (Q : List (K → ℤ)) (ht : e ≤ t + Q.length) :
    classNum (Sum.elim z z') (pairDiff j * H) Q W =
      ∑ μ ∈ H.support,
        H.coeff μ * vNumL W ((z j - z' j) :: (classList (Sum.elim z z') μ ++ Q)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«classNum_pairDiff_mul» := P2M_GroundTheory_Heights__Heights_NumbersDVR_classNum_pairDiff_mul_92ffd0efb78e
