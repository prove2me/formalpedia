-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_hasDerivAt_sq__f72e6668d75d
-- name    : P2M_GroundTheory_Heights__Heights_AnalyticLimit_hasDerivAt_sq__f72e6668d75d
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:43:46.884327+00:00
-- url     : https://prove2.me/theorems/a792e74c-8272-4ccf-b120-cfabf1cbb8e7
-- title:
--   P2 M Ground Theory Heights  Heights Analytic Limit has Deriv At sq  f72e6668d75d: P2 M Ground Theory Heights  Heights Analytic Limit has Deriv At sq  f72e6668d75d
-- statement:
--   The P2 M Ground Theory Heights  Heights Analytic Limit has Deriv At sq  f72e6668d75d construction uses the P2 M Ground Theory Heights  Heights Analytic Limit has Deriv At sq  f72e6668d75d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/PGreenMassReplaceLevi.lean#L84-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/PGreenMassReplaceLevi.lean#L84-L85

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

theorem P2M_GroundTheory_Heights__Heights_AnalyticLimit_hasDerivAt_sq__f72e6668d75d (x : ℝ) : HasDerivAt (fun x : ℝ => x ^ 2) (2 * x) x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AnalyticLimit».«hasDerivAt_sq'» := P2M_GroundTheory_Heights__Heights_AnalyticLimit_hasDerivAt_sq__f72e6668d75d
