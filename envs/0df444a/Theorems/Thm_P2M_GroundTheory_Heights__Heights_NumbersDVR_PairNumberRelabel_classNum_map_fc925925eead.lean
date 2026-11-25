-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_PairNumberRelabel_classNum_map_fc925925eead
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_PairNumberRelabel_classNum_map_fc925925eead
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:55:52.562255+00:00
-- url     : https://prove2.me/theorems/77446f2c-284e-56a1-9c91-62db3984140d
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Pair Number Relabel class Num map fc925925eead: P2 M Ground Theory Heights  Heights Numbers DVR Pair Number Relabel class Num map fc925925eead
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Pair Number Relabel class Num map fc925925eead construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Pair Number Relabel class Num map fc925925eead property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairNumberRelabel.lean#L172-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairNumberRelabel.lean#L172-L186

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsPairNumberRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_IntNumRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PRenameMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PRenameMultiProjPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PExistsUniqueRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPairNumberRelabel
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
open GroundTheory.Heights₂.Heights.NumbersDVR.PairNumberRelabel
variable {K₁ K₂ : Type} [DecidableEq K₁] [DecidableEq K₂] {ι₁ : K₁ → Type} {ι₂ : K₂ → Type}
  {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  (e : K₁ ≃ K₂) (σ : (Σ k, ι₁ k) ≃ (Σ k, ι₂ k))

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_PairNumberRelabel_classNum_map_fc925925eead (hσ : ∀ v, (σ v).1 = e v.1) {S : Type*} (cls : S → K₂ → ℤ)
    (H : MvPolynomial S ℤ) (Q : List (K₂ → ℤ)) (W : Ideal (MRing ι₁ O)) :
    classNum cls H Q (W.map (ren (R := O) σ : MRing ι₁ O →+* MRing ι₂ O)) =
      classNum (fun s => cls s ∘ e) H (Q.map (· ∘ e)) W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«PairNumberRelabel».«classNum_map» := P2M_GroundTheory_Heights__Heights_NumbersDVR_PairNumberRelabel_classNum_map_fc925925eead
