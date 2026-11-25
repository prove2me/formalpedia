-- Prove2me | Theorems.Thm_PI_MSC_rename_initMinor
-- name    : PI.MSC.rename_initMinor
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:35:58.044737+00:00
-- url     : https://prove2.me/theorems/d155a386-200c-43cf-ba19-e09f5b334a08
-- title:
--   MSC: rename init Minor
-- statement:
--   The MSC construction uses the rename init Minor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MinorSpanComplement/RenameInitMinor.lean#L23-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MinorSpanComplement/RenameInitMinor.lean#L23-L29

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

theorem PI.MSC.rename_initMinor (R : Type) [CommRing R] (N n s : ℕ) (hs : s ≤ n) (I : Fin s ↪o Fin N) :
    rename (phi N n) (initMinor R (r := N) (n := n) (fun p => I p) hs) = PI.minorX R N s I := by sorry
