-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_im_eq_re_mul_254c7de5cbad
-- name    : P2M_GroundTheory_Heights__Heights_AnalyticLimit_im_eq_re_mul_254c7de5cbad
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:44:02.926908+00:00
-- url     : https://prove2.me/theorems/c25da160-fb58-4118-a54a-0c4346d1963f
-- title:
--   P2 M Ground Theory Heights  Heights Analytic Limit im eq re mul 254c7de5cbad: P2 M Ground Theory Heights  Heights Analytic Limit im eq re mul 254c7de5cbad
-- statement:
--   The P2 M Ground Theory Heights  Heights Analytic Limit im eq re mul 254c7de5cbad construction uses the P2 M Ground Theory Heights  Heights Analytic Limit im eq re mul 254c7de5cbad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/PGreenMassReplaceLevi.lean#L55-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/PGreenMassReplaceLevi.lean#L55-L56

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

theorem P2M_GroundTheory_Heights__Heights_AnalyticLimit_im_eq_re_mul_254c7de5cbad (c : ℂ) : c.im = (-Complex.I * c).re := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AnalyticLimit».«im_eq_re_mul» := P2M_GroundTheory_Heights__Heights_AnalyticLimit_im_eq_re_mul_254c7de5cbad
