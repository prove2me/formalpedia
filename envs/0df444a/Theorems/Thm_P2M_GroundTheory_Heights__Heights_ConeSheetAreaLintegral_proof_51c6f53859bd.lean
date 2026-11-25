-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeSheetAreaLintegral_proof_51c6f53859bd
-- name    : P2M_GroundTheory_Heights__Heights_ConeSheetAreaLintegral_proof_51c6f53859bd
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:35:11.346544+00:00
-- url     : https://prove2.me/theorems/23a4d4fc-49fd-484b-80f8-97f39f405214
-- title:
--   P2 M Ground Theory Heights  Heights Cone Sheet Area Lintegral proof 51c6f53859bd: P2 M Ground Theory Heights  Heights Cone Sheet Area Lintegral proof 51c6f53859bd
-- statement:
--   The P2 M Ground Theory Heights  Heights Cone Sheet Area Lintegral proof 51c6f53859bd construction uses the P2 M Ground Theory Heights  Heights Cone Sheet Area Lintegral proof 51c6f53859bd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeSheetAreaLintegral.lean#L64-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeSheetAreaLintegral.lean#L64-L140

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeSheetAreaLintegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeSheetParam
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeMapArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeSheetAreaLintegral
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeIntegralMass_proof_0af09eb068df

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Matrix Filter Topology Set
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsGoodProj IsSheet fibre segre)
open scoped ENNReal

theorem P2M_GroundTheory_Heights__Heights_ConeSheetAreaLintegral_proof_51c6f53859bd (hPar : ConeSheetParam.Statement)
    (hArea : ConeMapArea.Statement) : ConeSheetAreaLintegral.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ConeSheetAreaLintegral».«proof» := P2M_GroundTheory_Heights__Heights_ConeSheetAreaLintegral_proof_51c6f53859bd
