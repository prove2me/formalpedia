-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartNormAlgClosed_algebraMap_localization_C_eccb7f2840c7
-- name    : P2M_GroundTheory_Heights__Heights_ChartNormAlgClosed_algebraMap_localization_C_eccb7f2840c7
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:07:41.374827+00:00
-- url     : https://prove2.me/theorems/84b8ab94-7971-4d3b-94fc-d468e59ae3da
-- title:
--   P2 M Ground Theory Heights  Heights Chart Norm Alg Closed algebra Map localization C eccb7f2840c7: P2 M Ground Theory Heights  Heights Chart Norm Alg Closed algebra Map localization C eccb7f2840c7
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Norm Alg Closed algebra Map localization C eccb7f2840c7 construction uses the P2 M Ground Theory Heights  Heights Chart Norm Alg Closed algebra Map localization C eccb7f2840c7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PChartNormAlgClosed.lean#L30-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PChartNormAlgClosed.lean#L30-L34

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsChartFirstGroupDvd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsChartNormAlgClosed
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsChartNormSep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PChartNormAlgClosed
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
open GroundTheory.Heights₂.Heights.ChartNormAlgClosed
variable {F : Type} [Field F] {n e : ℕ} (I : Ideal (MvPolynomial (Fin n) F)) (t : Fin n → F)
  (p : Ideal (MvPolynomial (Fin e × Fin n) F)) [p.IsPrime]

theorem P2M_GroundTheory_Heights__Heights_ChartNormAlgClosed_algebraMap_localization_C_eccb7f2840c7 (c : F) :
    algebraMap (MvPolynomial (Fin e × Fin n) F) (Localization.AtPrime p) (C c) =
      algebraMap F (Localization.AtPrime p) c := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartNormAlgClosed».«algebraMap_localization_C» := P2M_GroundTheory_Heights__Heights_ChartNormAlgClosed_algebraMap_localization_C_eccb7f2840c7
