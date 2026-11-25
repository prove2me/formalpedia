-- Prove2me | Theorems.Thm_P2M_HcInf_haar_unique__ccef7ee8667f
-- name    : P2M_HcInf_haar_unique__ccef7ee8667f
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:45:17.532+00:00
-- url     : https://prove2.me/theorems/895a4b0d-b07f-40ff-a95a-e4f28888566d
-- title:
--   P2 M Hc Inf haar unique  ccef7ee8667f: P2 M Hc Inf haar unique  ccef7ee8667f
-- statement:
--   The P2 M Hc Inf haar unique  ccef7ee8667f construction uses the P2 M Hc Inf haar unique  ccef7ee8667f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/CayDensExTop.lean#L127-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/CayDensExTop.lean#L127-L159

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_CayDensExSk
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_CayDensExTop
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
open NumberField IsDedekindDomain HcS.BasicNotions HcS.MainNotions HcS.MainNotions.StandardLattice HcS.MainNotions.GlobalTheoryTheory.GenusMassVolumes HcS.L2.Fam.SG.Tau
  HcS.L2.Fam.SG.Tau.InfCmpCut Matrix MeasureTheory Filter Topology
open scoped TensorProduct ENNReal NNReal
variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  (hc : CMData F E) (T : Type) [Fintype T] (cd : CDHaar)

theorem P2M_HcInf_haar_unique__ccef7ee8667f : HaarUnique F E hc T cd := by sorry

alias «HcInf».«haar_unique'» := P2M_HcInf_haar_unique__ccef7ee8667f
