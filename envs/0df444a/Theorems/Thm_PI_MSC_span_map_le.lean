-- Prove2me | Theorems.Thm_PI_MSC_span_map_le
-- name    : PI.MSC.span_map_le
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:35:24.053538+00:00
-- url     : https://prove2.me/theorems/2ff56a11-3c43-4e2c-b011-cec9b2c5b043
-- title:
--   MSC: span map le
-- statement:
--   The MSC construction uses the span map le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MinorSpanComplement/RenameInitMinor.lean#L59-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MinorSpanComplement/RenameInitMinor.lean#L59-L75

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_MinorSpanCompl
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSpanComplement_ExistsCoeffNeZeroOfMemSpan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSpanComplement_ShapeColumnDegreeColumnSizes
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_BideterminantMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSpanComplement_RenameInitMinor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open PI PI.MSC

theorem PI.MSC.span_map_le {σ : Type*} (R : Type) [CommRing R] {A B : Set (MvPolynomial σ ℤ)}
    (h : A ⊆ Submodule.span ℤ B) :
    Submodule.span R (MvPolynomial.map (Int.castRingHom R) '' A) ≤
      Submodule.span R (MvPolynomial.map (Int.castRingHom R) '' B) := by sorry
