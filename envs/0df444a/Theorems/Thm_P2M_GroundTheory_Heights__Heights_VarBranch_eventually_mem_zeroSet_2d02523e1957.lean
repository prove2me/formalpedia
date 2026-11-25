-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_VarBranch_eventually_mem_zeroSet_2d02523e1957
-- name    : P2M_GroundTheory_Heights__Heights_VarBranch_eventually_mem_zeroSet_2d02523e1957
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:43:55.442808+00:00
-- url     : https://prove2.me/theorems/15bbfba3-0acf-4407-bc56-65f6ade34b9c
-- title:
--   P2 M Ground Theory Heights  Heights Var Branch eventually mem zero Set 2d02523e1957: P2 M Ground Theory Heights  Heights Var Branch eventually mem zero Set 2d02523e1957
-- statement:
--   The P2 M Ground Theory Heights  Heights Var Branch eventually mem zero Set 2d02523e1957 construction uses the P2 M Ground Theory Heights  Heights Var Branch eventually mem zero Set 2d02523e1957 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSameOrderBranchesMeet.lean#L24-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSameOrderBranchesMeet.lean#L24-L41

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSameOrderBranchesMeet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchInCurveComponent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSameOrdersLiftCentre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchLift
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalModelExists
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSameOrderBranchesMeet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial ComplexSets Filter Topology

theorem P2M_GroundTheory_Heights__Heights_VarBranch_eventually_mem_zeroSet_2d02523e1957 {n : ℕ} {I : Ideal (MvPolynomial (Fin n) ℂ)} {q : Fin n → ℂ}
    (J : Ideal (MvPolynomial (Fin n) ℂ)) (c : VarBranch I 1 q) (h : ∀ f ∈ J, branchOrder c f = ⊤) :
    ∀ᶠ t in 𝓝 (0 : Fin 1 → ℂ), c.toFun t ∈ zeroSet J := by sorry

alias «GroundTheory».«Heights₂».«Heights».«VarBranch».«eventually_mem_zeroSet» := P2M_GroundTheory_Heights__Heights_VarBranch_eventually_mem_zeroSet_2d02523e1957
