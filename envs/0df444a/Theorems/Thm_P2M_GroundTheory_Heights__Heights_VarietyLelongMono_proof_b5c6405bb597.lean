-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_VarietyLelongMono_proof_b5c6405bb597
-- name    : P2M_GroundTheory_Heights__Heights_VarietyLelongMono_proof_b5c6405bb597
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:41:38.484412+00:00
-- url     : https://prove2.me/theorems/c5d42b22-380f-47cc-8542-b020e6ec2e33
-- title:
--   P2 M Ground Theory Heights  Heights Variety Lelong Mono proof b5c6405bb597: P2 M Ground Theory Heights  Heights Variety Lelong Mono proof b5c6405bb597
-- statement:
--   The P2 M Ground Theory Heights  Heights Variety Lelong Mono proof b5c6405bb597 construction uses the P2 M Ground Theory Heights  Heights Variety Lelong Mono proof b5c6405bb597 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PVarietyLelongMono.lean#L34-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PVarietyLelongMono.lean#L34-L73

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarietyLelongMono
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarWirtinger
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarLelongMono
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLinearNoetherNormalization
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PVarietyLelongMono
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
open MvPolynomial MeasureTheory Matrix ComplexSets
open scoped ENNReal
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_VarietyLelongMono_proof_b5c6405bb597 (hN : ComplexSets.LinearNoetherNormalization.Statement)
    (hW : VarWirtinger.Statement) (hM : VarLelongMono.Statement) : VarietyLelongMono.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«VarietyLelongMono».«proof» := P2M_GroundTheory_Heights__Heights_VarietyLelongMono_proof_b5c6405bb597
