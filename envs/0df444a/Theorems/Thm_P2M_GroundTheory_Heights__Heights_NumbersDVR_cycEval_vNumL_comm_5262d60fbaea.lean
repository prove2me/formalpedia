-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_cycEval_vNumL_comm_5262d60fbaea
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_cycEval_vNumL_comm_5262d60fbaea
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:21:01.861176+00:00
-- url     : https://prove2.me/theorems/d1ec95d9-948f-4ab7-b065-c1673e307bf3
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR cyc Eval v Num L comm 5262d60fbaea: P2 M Ground Theory Heights  Heights Numbers DVR cyc Eval v Num L comm 5262d60fbaea
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR cyc Eval v Num L comm 5262d60fbaea construction uses the P2 M Ground Theory Heights  Heights Numbers DVR cyc Eval v Num L comm 5262d60fbaea property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairNumberExpansionIndependence.lean#L42-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairNumberExpansionIndependence.lean#L42-L51

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_cycEval_vNumL_comm_5262d60fbaea (hC2 : VerticalDivisorsCommute.Statement.{0}) {O : Type} [CommRing O]
    [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O} (hϖ : Irreducible ϖ) {K : Type} [Fintype K]
    [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι O)} (l : List (K → ℤ))
    (hP : IsModelOver P (l.length + 1)) {b b' : K → ℤ} {f g f' g' : MRing ι O}
    (hD : IsVerticalDivisor P ϖ b f g) (hD' : IsVerticalDivisor P ϖ b' f' g') :
    cycEval (fun W => vNumL W (b' :: l)) (ratDiv P f g) =
      cycEval (fun W => vNumL W (b :: l)) (ratDiv P f' g') := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«cycEval_vNumL_comm» := P2M_GroundTheory_Heights__Heights_NumbersDVR_cycEval_vNumL_comm_5262d60fbaea
