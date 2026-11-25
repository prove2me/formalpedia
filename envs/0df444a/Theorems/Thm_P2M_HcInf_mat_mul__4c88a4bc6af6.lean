-- Prove2me | Theorems.Thm_P2M_HcInf_mat_mul__4c88a4bc6af6
-- name    : P2M_HcInf_mat_mul__4c88a4bc6af6
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:18:20.917711+00:00
-- url     : https://prove2.me/theorems/de80c8eb-c4d6-4f3d-95eb-a94385292927
-- title:
--   P2 M Hc Inf mat mul  4c88a4bc6af6: P2 M Hc Inf mat mul  4c88a4bc6af6
-- statement:
--   The P2 M Hc Inf mat mul  4c88a4bc6af6 construction uses the P2 M Hc Inf mat mul  4c88a4bc6af6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/CayDensExHua.lean#L51-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/CayDensExHua.lean#L51-L51

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_ContinuousAdelicGL2Det
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_CayDensExHua
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open HcInf
open HcS.BasicNotions Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal
attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
variable {P Q : ℕ}
local notation "Mat" => Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ

theorem P2M_HcInf_mat_mul__4c88a4bc6af6 (a b : UpqT P Q) : UpqT.mat (a * b) = UpqT.mat a * UpqT.mat b := by sorry

alias «HcInf».«mat_mul'» := P2M_HcInf_mat_mul__4c88a4bc6af6
