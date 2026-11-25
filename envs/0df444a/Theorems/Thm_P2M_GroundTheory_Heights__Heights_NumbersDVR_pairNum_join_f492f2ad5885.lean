-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_pairNum_join_f492f2ad5885
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_pairNum_join_f492f2ad5885
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:12:08.664868+00:00
-- url     : https://prove2.me/theorems/9834e8fd-b893-4360-8eab-2209b6718037
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR pair Num join f492f2ad5885: P2 M Ground Theory Heights  Heights Numbers DVR pair Num join f492f2ad5885
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR pair Num join f492f2ad5885 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR pair Num join f492f2ad5885 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PSubQuotient.lean#L34-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PSubQuotient.lean#L34-L65

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBundles
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSubQuotient
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
variable {K : Type*} [DecidableEq K] {ι : K → Type*}
  {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_pairNum_join_f492f2ad5885 {r m N : ℕ} (P : Ideal (MRing ι O)) (e : Fin r ⊕ Fin m ≃ Fin N)
    (xU xU' : Fin r → K → ℤ) (xV xV' : Fin m → K → ℤ) (fU gU : Fin r → MRing ι O)
    (fV gV : Fin m → MRing ι O) (k : ℕ) (Q : List (K → ℤ)) :
    pairNum P (fun i => Sum.elim xU xV (e.symm i)) (fun i => Sum.elim xU' xV' (e.symm i))
        (fun i => Sum.elim fU fV (e.symm i)) (fun i => Sum.elim gU gV (e.symm i))
        (psumExpansion N k) Q =
      pairNum P xU xU' fU gU (psumExpansion r k) Q + pairNum P xV xV' fV gV (psumExpansion m k) Q := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«pairNum_join» := P2M_GroundTheory_Heights__Heights_NumbersDVR_pairNum_join_f492f2ad5885
