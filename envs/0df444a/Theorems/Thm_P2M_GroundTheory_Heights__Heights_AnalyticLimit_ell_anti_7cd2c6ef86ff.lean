-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_ell_anti_7cd2c6ef86ff
-- name    : P2M_GroundTheory_Heights__Heights_AnalyticLimit_ell_anti_7cd2c6ef86ff
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:29:53.853126+00:00
-- url     : https://prove2.me/theorems/90dc347b-5bb6-4b64-9209-ce3df6b42a25
-- title:
--   P2 M Ground Theory Heights  Heights Analytic Limit ell anti 7cd2c6ef86ff: P2 M Ground Theory Heights  Heights Analytic Limit ell anti 7cd2c6ef86ff
-- statement:
--   The P2 M Ground Theory Heights  Heights Analytic Limit ell anti 7cd2c6ef86ff construction uses the P2 M Ground Theory Heights  Heights Analytic Limit ell anti 7cd2c6ef86ff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/Telescoping.lean#L28-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/Telescoping.lean#L28-L29

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_Telescoping
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
open ReciprocityTheory.AnForm.M (FinHolAtlas)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData ell errE)
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_AnalyticLimit_ell_anti_7cd2c6ef86ff {t t' : ℝ} (ht' : 0 < t') (htt : t' ≤ t) : ell t ≤ ell t' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AnalyticLimit».«ell_anti» := P2M_GroundTheory_Heights__Heights_AnalyticLimit_ell_anti_7cd2c6ef86ff
