-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HessCCompPluri_fderiv_fderiv_comp_apply_52a7820e256e
-- name    : P2M_GroundTheory_Heights__Heights_HessCCompPluri_fderiv_fderiv_comp_apply_52a7820e256e
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:18:35.657802+00:00
-- url     : https://prove2.me/theorems/343afa10-a698-4c9d-beb2-f89995fc918f
-- title:
--   P2 M Ground Theory Heights  Heights Hess CComp Pluri fderiv fderiv comp apply 52a7820e256e: P2 M Ground Theory Heights  Heights Hess CComp Pluri fderiv fderiv comp apply 52a7820e256e
-- statement:
--   The P2 M Ground Theory Heights  Heights Hess CComp Pluri fderiv fderiv comp apply 52a7820e256e construction uses the P2 M Ground Theory Heights  Heights Hess CComp Pluri fderiv fderiv comp apply 52a7820e256e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PHessCCompPluri.lean#L12-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PHessCCompPluri.lean#L12-L39

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHessCCompPluri
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PHessCCompPluri
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
open ReciprocityTheory.AnForm Filter Topology
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_HessCCompPluri_fderiv_fderiv_comp_apply_52a7820e256e {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℝ → ℝ} {L : E → ℝ} {z : E} (hF : ContDiffAt ℝ 2 F (L z)) (hL : ContDiffAt ℝ 2 L z)
    (v u : E) :
    fderiv ℝ (fderiv ℝ (fun w => F (L w))) z v u =
      deriv (deriv F) (L z) * (fderiv ℝ L z v * fderiv ℝ L z u) +
        deriv F (L z) * fderiv ℝ (fderiv ℝ L) z v u := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HessCCompPluri».«fderiv_fderiv_comp_apply» := P2M_GroundTheory_Heights__Heights_HessCCompPluri_fderiv_fderiv_comp_apply_52a7820e256e
