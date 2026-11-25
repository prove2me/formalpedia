-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_branchOrder_ne_top_of_not_mem_d78f2ff783ec
-- name    : P2M_GroundTheory_Heights__Heights_branchOrder_ne_top_of_not_mem_d78f2ff783ec
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:44:53.028088+00:00
-- url     : https://prove2.me/theorems/927cf348-3a15-43ec-9aef-f2f73c3d301a
-- title:
--   P2 M Ground Theory Heights  Heights branch Order ne top of not mem d78f2ff783ec: P2 M Ground Theory Heights  Heights branch Order ne top of not mem d78f2ff783ec
-- statement:
--   The P2 M Ground Theory Heights  Heights branch Order ne top of not mem d78f2ff783ec construction uses the P2 M Ground Theory Heights  Heights branch Order ne top of not mem d78f2ff783ec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSameOrdersLiftCentre.lean#L29-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSameOrdersLiftCentre.lean#L29-L45

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSameOrdersLiftCentre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSameOrdersLiftCentre
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
open MvPolynomial ComplexSets Filter Topology GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

theorem P2M_GroundTheory_Heights__Heights_branchOrder_ne_top_of_not_mem_d78f2ff783ec (hB : BranchOffHypersurface.Statement) {n : ℕ}
    {J : Ideal (MvPolynomial (Fin n) ℂ)} {q : Fin n → ℂ} (γ : VarBranch J 1 q) (hJ : J.IsPrime)
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (1 : ℕ)) {b : MvPolynomial (Fin n) ℂ} (hb : b ∉ J) :
    branchOrder γ b ≠ ⊤ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«branchOrder_ne_top_of_not_mem» := P2M_GroundTheory_Heights__Heights_branchOrder_ne_top_of_not_mem_d78f2ff783ec
