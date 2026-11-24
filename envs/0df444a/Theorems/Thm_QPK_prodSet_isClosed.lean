-- Prove2me | Theorems.Thm_QPK_prodSet_isClosed
-- name    : QPK.prodSet_isClosed
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T12:56:05.847013+00:00
-- url     : https://prove2.me/theorems/bf6e8474-ffd6-4ec0-9714-ad39fef03403
-- title:
--   QPK: prod Set is Closed
-- statement:
--   The QPK construction uses the prod Set is Closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilQuotientHaar/ProdSetIsClosed.lean#L22-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilQuotientHaar/ProdSetIsClosed.lean#L22-L31

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

theorem QPK.prodSet_isClosed {N H : Set G} (hN : IsClosed N) (hH : IsCompact H) :
    IsClosed (prodSet N H) := by sorry
