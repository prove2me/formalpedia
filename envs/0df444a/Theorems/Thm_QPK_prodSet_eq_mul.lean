-- Prove2me | Theorems.Thm_QPK_prodSet_eq_mul
-- name    : QPK.prodSet_eq_mul
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:54:31.934226+00:00
-- url     : https://prove2.me/theorems/6e6edf58-7d2e-502e-b3bc-36b0a001d52f
-- title:
--   QPK: prod Set eq mul
-- statement:
--   The QPK construction uses the prod Set eq mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilQuotientHaar/ProdSetIsClosed.lean#L13-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilQuotientHaar/ProdSetIsClosed.lean#L13-L20

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientHaar_HaarExist
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientHaar_ProdSetIsClosed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal Pointwise
open QPK
variable {G : Type} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]

theorem QPK.prodSet_eq_mul (N H : Set G) : prodSet N H = N * H := by sorry
