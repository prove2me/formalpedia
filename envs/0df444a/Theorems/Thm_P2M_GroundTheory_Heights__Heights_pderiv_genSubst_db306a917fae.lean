-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_pderiv_genSubst_db306a917fae
-- name    : P2M_GroundTheory_Heights__Heights_pderiv_genSubst_db306a917fae
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:49:30.061793+00:00
-- url     : https://prove2.me/theorems/a814e401-fd01-4bec-9a0d-a6af69457216
-- title:
--   P2 M Ground Theory Heights  Heights pderiv gen Subst db306a917fae: P2 M Ground Theory Heights  Heights pderiv gen Subst db306a917fae
-- statement:
--   The P2 M Ground Theory Heights  Heights pderiv gen Subst db306a917fae construction uses the P2 M Ground Theory Heights  Heights pderiv gen Subst db306a917fae property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChowFormBirational.lean#L29-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChowFormBirational.lean#L29-L40

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Imports
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChowFormBirational
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
open MvPolynomial
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_pderiv_genSubst_db306a917fae {K : Type*} [CommRing K] {n k : ℕ} (ζ c : Fin n → K) (i : Fin k) (m : Fin n)
    (j : Fin k × Fin n) :
    pderiv (i, m) (genSubst ζ c j) =
      (if j = (i, m) then 1 else 0) - (if j.1 = i then C (ζ m) * C (c j.2) else 0) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«pderiv_genSubst» := P2M_GroundTheory_Heights__Heights_pderiv_genSubst_db306a917fae
