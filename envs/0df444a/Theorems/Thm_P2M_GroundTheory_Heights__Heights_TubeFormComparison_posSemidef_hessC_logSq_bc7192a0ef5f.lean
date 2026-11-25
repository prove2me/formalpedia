-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_TubeFormComparison_posSemidef_hessC_logSq_bc7192a0ef5f
-- name    : P2M_GroundTheory_Heights__Heights_TubeFormComparison_posSemidef_hessC_logSq_bc7192a0ef5f
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:41:45.50946+00:00
-- url     : https://prove2.me/theorems/2f89a324-a7a3-411a-b5e4-10b9d8611f82
-- title:
--   P2 M Ground Theory Heights  Heights Tube Form Comparison pos Semidef hess C log Sq bc7192a0ef5f: P2 M Ground Theory Heights  Heights Tube Form Comparison pos Semidef hess C log Sq bc7192a0ef5f
-- statement:
--   The P2 M Ground Theory Heights  Heights Tube Form Comparison pos Semidef hess C log Sq bc7192a0ef5f construction uses the P2 M Ground Theory Heights  Heights Tube Form Comparison pos Semidef hess C log Sq bc7192a0ef5f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PTubeFormCompare.lean#L151-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PTubeFormCompare.lean#L151-L169

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCIsHermitian
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTubeFormCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_LogIntegrableOnOfLogIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PTubeFormCompare
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
open MvPolynomial Matrix Filter Topology ReciprocityTheory.AnForm ComplexSets
open scoped ContDiff ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.TubeFormComparison

theorem P2M_GroundTheory_Heights__Heights_TubeFormComparison_posSemidef_hessC_logSq_bc7192a0ef5f {m : ℕ} (P : MvPolynomial (Fin m) ℂ) (y : Fin m → ℂ)
    (hP : eval y P ≠ 0) : (hessC (fun z => logAbsSq P z ^ 2 / 2) y).PosSemidef := by sorry

alias «GroundTheory».«Heights₂».«Heights».«TubeFormComparison».«posSemidef_hessC_logSq» := P2M_GroundTheory_Heights__Heights_TubeFormComparison_posSemidef_hessC_logSq_bc7192a0ef5f
