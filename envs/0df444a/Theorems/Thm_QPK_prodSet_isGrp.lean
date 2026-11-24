-- Prove2me | Theorems.Thm_QPK_prodSet_isGrp
-- name    : QPK.prodSet_isGrp
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T12:56:10.776317+00:00
-- url     : https://prove2.me/theorems/bca4b547-a4f6-4d4a-97ed-8edd4b6abae0
-- title:
--   QPK: prod Set is Grp
-- statement:
--   The QPK construction uses the prod Set is Grp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilQuotientHaar/ProdSetIsClosed.lean#L33-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilQuotientHaar/ProdSetIsClosed.lean#L33-L47

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

theorem QPK.prodSet_isGrp {N H : Set G} (hN : IsGrp N) (hH : IsGrp H)
    (hnorm : ∀ h ∈ H, ∀ m ∈ N, h * m * h⁻¹ ∈ N) : IsGrp (prodSet N H) := by sorry
