-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_sq_norm_eq_re_im_995b20f7781c
-- name    : P2M_GroundTheory_Heights__Heights_AnalyticLimit_sq_norm_eq_re_im_995b20f7781c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:20:49.291193+00:00
-- url     : https://prove2.me/theorems/4f3409e9-cace-433d-9bde-5ac154cbb774
-- title:
--   P2 M Ground Theory Heights  Heights Analytic Limit sq norm eq re im 995b20f7781c: P2 M Ground Theory Heights  Heights Analytic Limit sq norm eq re im 995b20f7781c
-- statement:
--   The P2 M Ground Theory Heights  Heights Analytic Limit sq norm eq re im 995b20f7781c construction uses the P2 M Ground Theory Heights  Heights Analytic Limit sq norm eq re im 995b20f7781c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/PGreenMassReplaceLevi.lean#L80-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/PGreenMassReplaceLevi.lean#L80-L82

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_PGreenMassReplaceLevi
import Theorems.Thm_ReciprocityTheory_AnForm_levi_add_smul
import Theorems.Thm_ReciprocityTheory_AnForm_levi_re_analytic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.AnalyticLimit
open Filter Topology
open ReciprocityTheory.AnForm (levi levi_add_smul levi_re_analytic)
noncomputable section
variable {ι : Type} [Fintype ι]

theorem P2M_GroundTheory_Heights__Heights_AnalyticLimit_sq_norm_eq_re_im_995b20f7781c (c : ℂ) : ‖c‖ ^ 2 = c.re ^ 2 + 1 * c.im ^ 2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AnalyticLimit».«sq_norm_eq_re_im» := P2M_GroundTheory_Heights__Heights_AnalyticLimit_sq_norm_eq_re_im_995b20f7781c
